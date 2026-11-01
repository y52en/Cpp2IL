using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// W arithmetic is modulo2^32. Recover an exact cancelling pair while SSA
// definitions still identify values. Retain an explicit UInt32 view: a plain
// copy would incorrectly preserve the source X register's upper32 bits.
public static class NativeWord32IdentityRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            || method.ControlFlowGraph is not { } graph) return 0;
        return RecoverAll(method);
    }

    internal static int RecoverAll(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph) return 0;
        // Prove every pair against the same unchanged SSA graph. Eagerly
        // replacing (i-1)+1 first would hide the enclosing ((i-1)+1)-1 proof.
        var proven = graph.Instructions.Select(instruction =>
            (Instruction: instruction, Origin: TryOrigin(method, instruction, out var origin) ? origin : null))
            .Where(pair => pair.Origin != null).ToArray();
        foreach (var pair in proven) Apply(method, pair.Instruction, pair.Origin!);
        return proven.Length;
    }

    internal static bool TryRecover(MethodAnalysisContext method, Instruction outer)
    {
        if (!TryOrigin(method, outer, out var origin)) return false;
        Apply(method, outer, origin!);
        return true;
    }

    private static bool TryOrigin(MethodAnalysisContext method, Instruction outer, out LocalVariable? found)
    {
        found = null;
        if (method.ControlFlowGraph is not { } graph
            || outer is not { NativeArithmeticSize: 4, NativeFloatingPointSize: 0,
                NativeIntegerSourceView: false, Operands: [LocalVariable destination, LocalVariable intermediate, Immediate last] }
            || outer.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Xor)
            || method.ParameterLocals.Contains(destination)
            || graph.Instructions.Count(i => ReferenceEquals(i.Destination, destination)) != 1
            || intermediate.Type != null && intermediate.Type.FullName is not ("System.Int32" or "System.UInt32")
            || destination.Type != null && destination.Type.FullName is not ("System.Int32" or "System.UInt32")) return false;
        var definitions = graph.Instructions.Where(i => ReferenceEquals(i.Destination, intermediate)).ToArray();
        if (definitions is not [Instruction { NativeArithmeticSize: 4, NativeFloatingPointSize: 0,
                NativeIntegerSourceView: false, Operands: [_, LocalVariable origin, Immediate first] } inner]
            || ReferenceEquals(origin, destination) || ReferenceEquals(origin, intermediate)
            || origin.Type != null && origin.Type.FullName is not ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64")
            || first.Value != last.Value || first.Value is < int.MinValue or > uint.MaxValue
            || !((inner.OpCode == OpCode.Add && outer.OpCode == OpCode.Subtract)
                || (inner.OpCode == OpCode.Subtract && outer.OpCode == OpCode.Add)
                || (inner.OpCode == OpCode.Xor && outer.OpCode == OpCode.Xor))
            || !ForwardNullCheckRecovery.DefinitionDominates(graph, inner, outer)) return false;
        var origins = graph.Instructions.Where(i => ReferenceEquals(i.Destination, origin)).ToArray();
        if (method.ParameterLocals.Contains(origin) ? origins.Length != 0 : origins.Length != 1
                || !ForwardNullCheckRecovery.DefinitionDominates(graph, origins[0], inner)) return false;
        found = origin;
        return true;
    }

    private static void Apply(MethodAnalysisContext method, Instruction outer, LocalVariable origin)
    {
        var destination = (LocalVariable)outer.Operands[0];
        // No graph mutation before all width, SSA, type and dominance proofs.
        var types = method.AppContext.SystemTypes;
        outer.OpCode = OpCode.NumericConvert;
        outer.SetOperands(destination, types.SystemUInt32Type, types.SystemUInt64Type, origin);
        outer.NativeIntegerSourceView = true;
        outer.NativeArithmeticSize = 0;
        destination.Type = types.SystemUInt32Type;
    }
}
