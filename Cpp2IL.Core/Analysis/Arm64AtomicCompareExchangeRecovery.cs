using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Original ARM64 acquire/release compare-exchange: return the observed old
// word, update only on equality, retry failed exclusive stores. Never lower
// this to a load/compare/store sequence or discard its memory ordering.
public static class Arm64AtomicCompareExchangeRecovery
{
    private static readonly byte[] Body = Convert.FromHexString(
        "e80300aa00fd5fc81f0002eb8100005401fd09c889ffff35c0035fd65f3f03d5c0035fd6");
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, Lazy<bool>> Profiles = new();

    private static bool Supports(ApplicationAnalysisContext app) =>
        Profiles.GetValue(app, owner => new Lazy<bool>(() => CheckedUnboxRecovery.Supports(owner)
            && owner.Metadata.BaseStream is MemoryStream metadata
            && Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(
                "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",
                StringComparison.OrdinalIgnoreCase))).Value;

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not {} graph) return 0;
        var calls = graph.Instructions.Where(i => i is { OpCode: OpCode.Call,
            Operands: [Immediate { UnsignedValue: 0xACC538 or 0xACC55C }, ..] }).ToArray();
        if (calls.Length == 0 || !Supports(method.AppContext)) return 0;
        var count = 0;
        foreach (var call in calls)
        {
            var address = ((Immediate)call.Operands[0]).UnsignedValue;
            var binary = method.AppContext.Binary;
            if (!binary.TryMapVirtualAddressToRaw(address, out var offset)
                || offset < 0 || offset > binary.RawLength - Body.Length
                || !binary.GetRawBinaryContent().Slice((int)offset, Body.Length).SequenceEqual(Body)) continue;
            if (TryRewrite(method, call, true)) count++;
        }
        return count;
    }

    internal static bool TryRewrite(MethodAnalysisContext method, Instruction call, bool originalHelperProven)
    {
        if (!originalHelperProven || !call.HasArm64DirectArgumentSnapshot || call.NativeVirtualDispatch
            || call.NativeDirectCallTarget is not (0xACC538 or 0xACC55C)
            || call.Operands[1] is not LocalVariable result
            || method.ControlFlowGraph is not {} graph
            || graph.Instructions.Count(i => ReferenceEquals(i.Destination, result)) != 1) return false;
        var location = ResolveManagedLocation(method, call);
        if (location == null) return false;
        var element = location switch
        {
            LocalVariable { Type: ByRefTypeAnalysisContext byref } => byref.ElementType,
            AddressOf { Target: LocalVariable local } => local.Type,
            AddressOf { Target: FieldReference field } when field.Field.BackingData != null => field.Field.FieldType,
            _ => null,
        };
        if (element == null || element.HasAnyGenericParameters()
            || element is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
            || element.FullName is not ("System.Int64" or "System.IntPtr")
                && !NullBypassRuntimeCastRecovery.ReferenceType(element)
            || !Compatible(call.Operands[3], element)
                && !Arm64AtomicReferenceProof.Prove(method, call, call.Operands[3], element)
            || !Compatible(call.Operands[4], element)
                && !Arm64AtomicReferenceProof.Prove(method, call, call.Operands[4], element)
            || result.Type != null && !TrivialConstructorRecovery.SameType(result.Type, element)
                && !NullBypassRuntimeCastRecovery.ReferenceType(result.Type)) return false;
        var matches = new List<MethodAnalysisContext>();
        // Bind the actual corlib declaration, never an injected namesake or a
        // guessed native-address alias. Close generic T from managed storage.
        foreach (var owner in method.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly.Types
            .Where(t => t.FullName == "System.Threading.Interlocked"))
        foreach (var candidate in owner.Methods.Where(m => m.Name == "CompareExchange"
            && m.Definition != null && m.IsStatic && m.Parameters.Count == 3))
        {
            MethodAnalysisContext target;
            if (element.IsValueType)
            {
                if (candidate.GenericParameters.Count != 0) continue;
                target = candidate;
            }
            else
            {
                if (candidate.GenericParameters.Count != 1) continue;
                target = new ConcreteGenericMethodAnalysisContext(candidate, [], [element]);
            }
            if (TrivialConstructorRecovery.SameType(target.ReturnType, element)
                && target.Parameters[0].ParameterType is ByRefTypeAnalysisContext first
                && TrivialConstructorRecovery.SameType(first.ElementType, element)
                && TrivialConstructorRecovery.SameType(target.Parameters[1].ParameterType, element)
                && TrivialConstructorRecovery.SameType(target.Parameters[2].ParameterType, element)) matches.Add(target);
        }
        if (matches.Count != 1) return false;
        var blocks = graph.Blocks.Where(b => b.Instructions.Contains(call)).ToArray();
        if (blocks.Length != 1) return false;
        var arguments = new[] { call.Operands[3], call.Operands[4] };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (Compatible(arguments[i], element)) continue;
            // This view cannot newly throw: every incoming SSA path was
            // proved null/exactly T above. Keep the original native checks
            // and their exception transport; never narrow the producer shared
            // with other consumers or emit an unchecked ref variance cast.
            var name = "atomic_reference_" + method.Locals.Count;
            var view = new LocalVariable(name, new(null, name), element);
            method.Locals.Add(view);
            blocks[0].Instructions.Insert(blocks[0].Instructions.IndexOf(call),
                new(call.Index, OpCode.CastClass, view, element, arguments[i]));
            arguments[i] = view;
        }
        // Physical input slots are certified before SSA; trailing raw registers
        // are not helper inputs. Their producers/effects remain in the graph.
        call.SetOperands(matches[0], result, location, arguments[0], arguments[1]);
        result.Type = element;
        return true;
    }

    internal static IOperand? ResolveManagedLocation(MethodAnalysisContext method, Instruction call)
        => ResolveManagedAddress(method, call, call.Operands[2]);

    internal static IOperand? ResolveManagedAddress(MethodAnalysisContext method, Instruction consumer, IOperand original)
    {
        if (original is AddressOf or LocalVariable { Type: ByRefTypeAnalysisContext }) return original;
        if (original is not LocalVariable value || method.ControlFlowGraph is not {} graph) return null;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);
        var seen = new HashSet<LocalVariable>();
        while (seen.Add(value) && seen.Count <= 8
            && definitions.TryGetValue(value, out var definition) && definition != null)
        {
            if (!ForwardNullCheckRecovery.DefinitionDominates(graph, definition, consumer)) return null;
            if (definition is { OpCode: OpCode.Move, NativeReadSize: 0, NativeWriteSize: 0,
                    NativeRegisterCopySize: 8, Operands: [LocalVariable, LocalVariable copied] })
            { value = copied; consumer = definition; continue; }
            if (definition is not { OpCode: OpCode.Add, NativeReadSize: 0, NativeWriteSize: 0,
                    NativeArithmeticSize: 8,
                    Operands: [LocalVariable, LocalVariable receiver, Immediate { Value: >= 16 and <= int.MaxValue } displacement] }
                || displacement.Value % 8 != 0
                || receiver.Type is not { IsValueType: false, Definition: not null } owner
                || owner.IsInterface || owner.HasAnyGenericParameters()
                || !NullBypassRuntimeCastRecovery.ReferenceType(owner)) return null;
            var offset = (int)displacement.Value;
            var matches = new List<FieldAnalysisContext>();
            var hierarchy = new HashSet<TypeAnalysisContext>();
            for (var type = owner; type != null; type = type.BaseType)
            {
                if (!hierarchy.Add(type) || hierarchy.Count > 32 || type.HasAnyGenericParameters()) return null;
                foreach (var field in type.Fields.Where(f => !f.IsStatic))
                {
                    if (field.BackingData == null || field.Offset != field.DefaultOffset || field.Offset < 0
                        || field.Attributes != field.DefaultAttributes
                        || !TrivialConstructorRecovery.SameType(field.FieldType, field.DefaultFieldType)) return null;
                    if (field.Offset >= offset + 8L) continue;
                    var size = !field.FieldType.IsValueType ? 8 : TypeSizes.UnboxedSize(field.FieldType, 8);
                    if (size <= 0) return null;
                    if (field.Offset + size <= offset) continue;
                    // Reject explicit-layout overlap, interior slots, partial
                    // fields and another field intersecting these eight bytes.
                    if (field.Offset != offset || size != 8) return null;
                    matches.Add(field);
                }
            }
            if (matches.Count != 1) return null;
            var target = matches[0];
            if (target.Attributes.HasFlag(FieldAttributes.InitOnly)
                || target.Attributes.HasFlag(FieldAttributes.Literal)
                || target.Visibility != FieldAttributes.Public
                    && !TrivialConstructorRecovery.SameType(target.DeclaringType, method.DeclaringType)) return null;
            return new AddressOf(new FieldReference(target, receiver, offset));
        }
        return null;
    }

    private static bool Compatible(IOperand value, TypeAnalysisContext type) => value switch
    {
        LocalVariable local => TrivialConstructorRecovery.SameType(local.Type, type),
        Immediate { Value: 0 } => !type.IsValueType,
        _ => false,
    };
}
