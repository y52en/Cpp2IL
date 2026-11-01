using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A native scalar register can hold a small value type's representation. CIL
// cannot perform integer operations on that struct. Project only through a
// public getter whose complete original implementation proves the operation.
// Ordinary struct copies, raw DateTime flags, and unproved getters stay intact.
public static class NativeScalarValueRecovery
{
    internal const long TicksMask = 0x3fffffffffffffff;
    private static readonly byte[] MaskedGetterBytes = Convert.FromHexString("080840F900F54092C0035FD6");
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, Lazy<bool>> Profiles = new();

    private static bool Profile(ApplicationAnalysisContext app) => Profiles.GetValue(app, a => new Lazy<bool>(() =>
        a.UnityVersion.Major == 2018 && a.UnityVersion.Minor == 4 && CheckedUnboxRecovery.Supports(a)
        && a.Metadata.BaseStream is MemoryStream metadata
        && Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(
            "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e", StringComparison.OrdinalIgnoreCase))).Value;

    private static TypeAnalysisContext? TypeOf(IOperand operand) => operand switch
    { LocalVariable v => v.Type, FieldReference f => f.Field.FieldType, _ => null };

    private static bool Aggregate(TypeAnalysisContext? type) => type is { IsValueType: true }
        && !type.IsEnumType && !type.HasAnyGenericParameters() && !TypeSizes.IsScalarValueType(type);

    internal static MethodAnalysisContext? ProveMaskedGetter(MethodAnalysisContext getter, FieldAnalysisContext field,
        long mask, byte[] bytes, bool originalField)
    {
        var owner = field.DeclaringType;
        if (!originalField || mask != TicksMask || !Aggregate(owner) || owner.IsGenericInstance
            || (owner.Attributes & TypeAttributes.VisibilityMask) is not (TypeAttributes.Public or TypeAttributes.NestedPublic)
            || owner.Fields.Count(f => !f.IsStatic) != 1 || field.IsStatic || field.Offset != 0
            || field.FieldType.FullName is not ("System.Int64" or "System.UInt64")
            || !ReferenceEquals(getter.DeclaringType, owner) || getter.IsStatic || getter.IsVirtual
            || getter.Visibility != MethodAttributes.Public || getter.Parameters.Count != 0
            || getter.GenericParameters.Count != 0 || getter.UnderlyingPointer == 0
            || ((int)getter.ImplAttributes & 0x1027) != 0 || ((int)getter.Attributes & 0x6000) != 0
            || getter.ReturnType.FullName != "System.Int64"
            || owner.Properties.Count(p => ReferenceEquals(p.Getter, getter)) != 1
            || !bytes.AsSpan().SequenceEqual(MaskedGetterBytes)) return null;
        // LDR X8,[boxed-this+16]; AND X0,X8,#low62; RET. No calls,
        // writes, branches, checked conversions, or hidden side effects.
        return getter;
    }

    private static MethodAnalysisContext? FindMaskedGetter(TypeAnalysisContext owner, long mask)
    {
        if (mask != TicksMask || owner.IsGenericInstance || !Aggregate(owner) || TypeSizes.UnboxedSize(owner, 8) != 8) return null;
        var fields = owner.Fields.Where(f => !f.IsStatic).ToArray();
        if (fields is not [FieldAnalysisContext { BackingData: not null } field]) return null;
        var binary = owner.AppContext.Binary;
        var matches = owner.Methods.Where(getter => getter.UnderlyingPointer != 0
            && binary.TryMapVirtualAddressToRaw(getter.UnderlyingPointer, out var offset)
            && offset >= 0 && offset <= binary.RawLength - MaskedGetterBytes.Length
            && ProveMaskedGetter(getter, field, mask,
                binary.GetRawBinaryContent().Slice((int)offset, MaskedGetterBytes.Length).ToArray(), true) != null).ToArray();
        return matches.Length == 1 ? matches[0] : null;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg || !cfg.Instructions.Any(i => i.NativeArithmeticSize == 8
            && i.OpCode is OpCode.And or OpCode.Add or OpCode.Subtract
            && i.Sources.Any(o => Aggregate(TypeOf(o)))) || !Profile(method.AppContext)) return 0;
        return Recover(method, FindMaskedGetter, type => NativeScalarStructComparison.Find(type, 8));
    }

    // Production supplies only authenticated original getters. Tests inject
    // already-proved metadata getters to exercise CFG/operand preservation.
    internal static int Recover(MethodAnalysisContext method,
        Func<TypeAnalysisContext, long, MethodAnalysisContext?> masked,
        Func<TypeAnalysisContext, MethodAnalysisContext?> raw)
    {
        if (method.ControlFlowGraph is not { } cfg) return 0;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.Count());
        var dominance = new DominatorInfo(cfg);
        var count = 0;
        foreach (var block in cfg.Blocks)
        foreach (var instruction in block.Instructions.ToArray())
        {
            if (instruction.NativeArithmeticSize != 8 || instruction.NativeFloatingPointSize != 0
                || instruction.Operands is not [LocalVariable destination, var left, var right]
                || !definitions.TryGetValue(destination, out var writes) || writes != 1
                || destination.Type != null && destination.Type.FullName is not ("System.Int64" or "System.UInt64")) continue;
            if (instruction.OpCode == OpCode.And)
            {
                var source = right is Immediate ? left : right;
                if ((right is Immediate ? right : left) is not Immediate mask || !Aggregate(TypeOf(source))
                    || masked(TypeOf(source)!, mask.Value) is not { } getter) continue;
                if (ProjectAtFieldRead(method, block, instruction, source, getter, destination, dominance))
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                }
                else
                {
                    instruction.OpCode = OpCode.Call;
                    instruction.SetOperands(getter, destination, new AddressOf(source));
                }
                destination.Type ??= getter.ReturnType;
                count++;
            }
            else if (instruction.OpCode is OpCode.Add or OpCode.Subtract)
            {
                var projected = false;
                for (var n = 1; n <= 2; n++)
                {
                    var operand = instruction.Operands[n];
                    if (!Aggregate(TypeOf(operand)) || raw(TypeOf(operand)!) is not { } getter) continue;
                    var scalar = new LocalVariable("native_scalar_" + method.Locals.Count,
                        new(null, "native_scalar_" + method.Locals.Count), getter.ReturnType);
                    method.Locals.Add(scalar);
                    if (!ProjectAtFieldRead(method, block, instruction, operand, getter, scalar, dominance))
                        block.Instructions.Insert(block.Instructions.IndexOf(instruction),
                            new Instruction(instruction.Index, OpCode.Call, getter, scalar, new AddressOf(operand)));
                    instruction.SetOperand(n, scalar);
                    projected = true; count++;
                }
                if (projected) destination.Type ??= method.AppContext.SystemTypes.SystemInt64Type;
            }
        }
        return count;
    }

    // Project AT the original read, rather than reread a field at its later
    // use. Thus interleaved writes, calls and control flow keep the original
    // snapshot semantics. Only an authenticated read-only getter is supplied.
    private static bool ProjectAtFieldRead(MethodAnalysisContext method, Block block, Instruction use,
        IOperand operand, MethodAnalysisContext getter, LocalVariable result, DominatorInfo dominance)
    {
        if (operand is not LocalVariable local || method.ParameterLocals.Contains(local)) return false;
        var producers = method.ControlFlowGraph!.Blocks.SelectMany(b => b.Instructions
            .Where(i => ReferenceEquals(i.Destination, local)).Select(i => (Block: b, Instruction: i))).ToArray();
        if (producers.Length != 1 || producers[0].Instruction is not
            { OpCode: OpCode.Move, NativeReadSize: 8, Operands: [LocalVariable _, FieldReference field] } load
            || field.Parent != null || field.Field.IsStatic
            || field.Local.Type is not ByRefTypeAnalysisContext receiver
            || !receiver.ElementType.IsValueType || !ReferenceEquals(receiver.ElementType, field.Field.DeclaringType)
            || !ReferenceEquals(field.Field.FieldType, local.Type)
            || ReferenceEquals(field.Local, local)) return false;
        var home = producers[0].Block;
        if (ReferenceEquals(home, block)
            ? home.Instructions.IndexOf(load) >= block.Instructions.IndexOf(use)
            : !dominance.Dominates(home, block)) return false;

        // The temporary must have exactly this definition and this one use.
        // Inspect compound operands too; an address hidden in a call argument,
        // nested field or memory operand must retain snapshot semantics.
        if (use.Operands.Count(o => ReferenceEquals(o, local)) != 1
            || method.ControlFlowGraph!.Instructions.Any(i => !ReferenceEquals(i, load) && !ReferenceEquals(i, use)
                && i.Operands.Any(o => MayMention(o, local, 0)))) return false;
        load.OpCode = OpCode.Call;
        load.SetOperands(getter, result, new AddressOf(field));
        return true;
    }

    private static bool MayMention(IOperand? operand, LocalVariable local, int depth)
    {
        if (depth > 16) return true;
        return operand switch
        {
            null => false,
            LocalVariable value => ReferenceEquals(value, local),
            AddressOf address => MayMention(address.Target, local, depth + 1),
            FieldReference field => ReferenceEquals(field.Local, local) || MayMention(field.Parent, local, depth + 1),
            MemoryOperand memory => MayMention(memory.Base, local, depth + 1) || MayMention(memory.Index, local, depth + 1),
            ArrayAccess element => ReferenceEquals(element.Array, local) || MayMention(element.Index, local, depth + 1),
            ArrayLength length => ReferenceEquals(length.Array, local),
            Immediate or FloatLiteral or DoubleLiteral or StringLiteral or Register or StackOffset
                or DefaultStructValue or MethodAnalysisContext or TypeAnalysisContext or Instruction or Block => false,
            _ => true
        };
    }
}
