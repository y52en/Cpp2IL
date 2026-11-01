using System;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Analysis;

// Full original C and four instructions inspected: set has_value at +4,
// store W1 at +0, return. A stale MethodInfo in X3 must not turn this call
// into the previous delegate's constructor. No name/address-only matching.
public static class NativeNullableConstructorRecovery
{
    internal static int PrepareStackReceivers(MethodAnalysisContext method)
    {
        var count = 0;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        foreach (var call in block.Instructions.ToArray())
            if (call.IsCall && call.Operands[0] is Immediate target
                && IsProvenBody(method, target.UnsignedValue) && ScheduleStackReceiver(block, call)) count++;
        return count;
    }

    internal static bool ScheduleStackReceiver(Block block, Instruction call, bool requireZeroInitialization = true)
    {
        var first = call.OpCode == OpCode.Call ? 2 : 1;
        if (!call.IsCall || call.Operands.Count <= first || call.Operands[first] is not Register { Name: "X0", Version: -1 }) return false;
        var end = block.Instructions.IndexOf(call);
        for (var at = end - 1; at >= 0; at--)
        {
            var definition = block.Instructions[at];
            if (definition.IsCall) return false;
            if (definition.Destination is not Register { Name: "X0" }) continue;
            if (definition is not { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: Register storage }] }
                || !storage.Name.StartsWith("stack_", StringComparison.Ordinal) || storage.Version != -1) return false;
            var initialized = false;
            foreach (var between in block.Instructions.Skip(at + 1).Take(end - at - 1))
            {
                if (between.IsCall || between.OpCode != OpCode.Move
                    || between.Operands.Any(UsesX0)
                    || between.ImplicitDefinition is Register { Name: "X0" }) return false;
                if (between.Destination is Register target && target.Number == storage.Number)
                {
                    if (between.NativeWriteSize != 8
                        || requireZeroInitialization && between.Operands[1] is not Immediate { Value: 0 }) return false;
                    initialized = true;
                }
            }
            if (!initialized) return false;
            // Address computation is pure, uses the same normalized stack cell,
            // and X0 is unused until this proven full-field constructor call.
            // Compute it after initialization so SSA's address clobber versions
            // the storage that the subsequent load actually reads.
            block.Instructions.RemoveAt(at);
            block.Instructions.Insert(block.Instructions.IndexOf(call), definition);
            return true;
        }
        return false;
    }

    private static bool UsesX0(IOperand operand) => operand switch
    {
        Register { Name: "X0" } => true,
        MemoryOperand memory => memory.Base != null && UsesX0(memory.Base)
            || memory.Index != null && UsesX0(memory.Index),
        AddressOf address => UsesX0(address.Target),
        _ => false
    };

    internal static bool MatchesBody(ReadOnlySpan<byte> body) => body.SequenceEqual(
        new byte[] { 0xe8, 0x03, 0x00, 0x32, 0x08, 0x10, 0x00, 0x39,
            0x01, 0x00, 0x00, 0xb9, 0xc0, 0x03, 0x5f, 0xd6 });

    // True reserves the proven native body even if its real X2 metadata has
    // not propagated yet. The generic last-MethodInfo fallback MUST wait.
    internal static bool IsProvenBody(MethodAnalysisContext caller, ulong entry)
    {
        var app = caller.AppContext;
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.PointerSizeBytes != 8
            || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return false;
        try
        {
            if (!app.Binary.TryMapVirtualAddressToRaw(entry, out var offset)
                || offset < 0 || offset > int.MaxValue || offset > app.Binary.RawLength - 16) return false;
            return MatchesBody(app.Binary.GetRawBinaryContent().Slice((int)offset, 16));
        }
        catch (Exception) { return false; }
    }

    internal static bool TryResolve(MethodAnalysisContext caller, Instruction call)
    {
        var first = call.OpCode == OpCode.Call ? 2 : 1;
        if (!call.IsCall || call.NativeVirtualDispatch || call.Operands[0] is not Immediate
            || call.Operands.Count < first + 3 || call.Operands.Count > first + 16) return false;
        var metadata = call.Operands[first + 2] switch
        {
            RuntimeMethodInfoAnalysisContext direct => direct,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext local } => local,
            _ => null
        };
        if (metadata?.RepresentedMethod is not ConcreteGenericMethodAnalysisContext ctor
            || !Contract(ctor)) return false;
        var graph = caller.ControlFlowGraph!;
        var block = graph.Blocks.SingleOrDefault(b => b.Instructions.Contains(call));
        if (block == null) return false;
        var pointer = call.Operands[first];
        for (var depth = 0; depth < 8 && pointer is LocalVariable local; depth++)
        {
            var definitions = block.Instructions.Take(block.Instructions.IndexOf(call))
                .Where(i => ReferenceEquals(i.Destination, local)).ToArray();
            if (definitions is not [{ OpCode: OpCode.Move, Operands: [_, var source] }]) return false;
            pointer = source;
        }
        if (pointer is not AddressOf { Target: LocalVariable storage }
            || storage.Type != null && !TrivialConstructorRecovery.SameType(storage.Type, ctor.DeclaringType)) return false;
        // This native void helper preserves X0. Do not discard a live raw
        // return-register definition without a separate SSA preservation proof.
        if (call.Destination is { } result && graph.Instructions.Any(i => !ReferenceEquals(i, call)
                && i.Sources.Any(s => ReferenceEquals(s, result)))) return false;
        call.SetOperand(0, ctor);
        // Exact ARM64 ABI: byref this, one I4 enum, MethodInfo in X2.
        // Discard only stale caller-saved registers, never another real arg.
        call.SetOperands(call.Operands.Take(first + 3).ToList());
        return true;
    }

    internal static bool Contract(MethodAnalysisContext method)
    {
        if (method is not ConcreteGenericMethodAnalysisContext ctor
            || ctor.IsStatic || ctor.Name != ".ctor" || !ctor.IsVoid || ctor.Parameters.Count != 1
            || ctor.MethodGenericParameters.Count != 0
            || ctor.DeclaringType is not GenericInstanceTypeAnalysisContext owner
            || !OwnerContract(owner)
            || !TrivialConstructorRecovery.SameType(ctor.Parameters[0].ParameterType, owner.GenericArguments[0])) return false;
        return true;
    }

    internal static bool OwnerContract(GenericInstanceTypeAnalysisContext owner)
    {
        if (owner.GenericType.FullName != "System.Nullable`1" || !owner.IsValueType
            || owner.HasAnyGenericParameters() || owner.GenericArguments.Count != 1
            || owner.GenericArguments[0] is not { IsEnumType: true } enumeration
            || enumeration.EnumUnderlyingType?.FullName is not ("System.Int32" or "System.UInt32")) return false;
        var fields = ClosedGenericValueLayout.Fields(owner, 8);
        return fields is { Count: 2 }
            && fields[0].Offset == 0 && fields[0].Size == 4
            && TrivialConstructorRecovery.SameType(fields[0].Field.FieldType, enumeration)
            && fields[1].Offset == 4 && fields[1].Size == 1
            && fields[1].Field.FieldType.FullName == "System.Boolean"
            && ClosedGenericValueLayout.TryGet(owner, 8)?.Size == 8;
    }
}
