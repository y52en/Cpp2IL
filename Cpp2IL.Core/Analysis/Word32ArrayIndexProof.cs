using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// An unsigned W bounds comparison and an SXTW address index test/use the same
// low32 bits. Prove actual conversion definitions, never register names or
// similar expression text. This helper is read-only; all arithmetic and the
// original bounds branch remain in the caller's graph.
internal static class Word32ArrayIndexProof
{
    private static bool Integral(LocalVariable local) => local.Type?.FullName is
        "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64";

    private static Instruction? Definition(MethodAnalysisContext method, LocalVariable local, Instruction use)
    {
        if (method.ControlFlowGraph is not { } graph) return null;
        var definitions = graph.Instructions.Where(i => ReferenceEquals(i.Destination, local)).ToArray();
        return definitions.Length == 1
            && ForwardNullCheckRecovery.DefinitionDominates(graph, definitions[0], use) ? definitions[0] : null;
    }

    private static bool WordSource(MethodAnalysisContext method, LocalVariable value, Instruction use)
    {
        if (value.Type != null && !Integral(value) || method.ControlFlowGraph is not { } graph) return false;
        if (graph.Instructions.Any(i => i.Operands.Any(o => AddressTaken(o, value)))) return false;
        var definitions = graph.Instructions.Where(i => ReferenceEquals(i.Destination, value)).ToArray();
        if (method.ParameterLocals.Contains(value)) return Integral(value) && definitions.Length == 0;
        return definitions.Length == 1 && ForwardNullCheckRecovery.DefinitionDominates(graph, definitions[0], use)
            && (Integral(value) || definitions[0].NativeArithmeticSize == 4 && definitions[0].NativeFloatingPointSize == 0
                && definitions[0].OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.And or OpCode.Or or OpCode.Xor);
    }

    internal static bool PureConversion(MethodAnalysisContext method, Instruction instruction)
    {
        if (instruction is not { OpCode: OpCode.NumericConvert, NativeArithmeticSize: 0, NativeFloatingPointSize: 0,
            Operands: [LocalVariable output, TypeAnalysisContext target, TypeAnalysisContext source, LocalVariable value] }
            || output.Type == null || output.Type.FullName != target.FullName
            || ReferenceEquals(output, value)) return false;
        if (instruction.NativeIntegerSourceView)
            return target.FullName is "System.Int32" or "System.UInt32" && source.FullName == "System.UInt64"
                && WordSource(method, value, instruction);
        return target.FullName == "System.Int64" && source.FullName == "System.Int32"
            && value.Type?.FullName == "System.Int32" && WordSource(method, value, instruction);
    }

    internal static bool SameIndex(MethodAnalysisContext method, Instruction? comparison,
        IOperand checkedIndex, IOperand storedIndex, Instruction store)
    {
        if (comparison is not { OpCode: OpCode.CheckLess, NativeComparisonSize: 4, UnsignedComparison: true }
            || checkedIndex is not LocalVariable checkedLocal || storedIndex is not LocalVariable storedLocal
            || Definition(method, checkedLocal, comparison) is not { NativeIntegerSourceView: true,
                Operands: [_, TypeAnalysisContext { FullName: "System.UInt32" }, _, LocalVariable checkedSource] } checkView
            || !PureConversion(method, checkView)
            || Definition(method, storedLocal, store) is not { NativeIntegerSourceView: false,
                Operands: [_, TypeAnalysisContext { FullName: "System.Int64" }, _, LocalVariable narrow] } wideView
            || !PureConversion(method, wideView)
            || Definition(method, narrow, wideView) is not { NativeIntegerSourceView: true,
                Operands: [_, TypeAnalysisContext { FullName: "System.Int32" }, _, LocalVariable storedSource] } narrowView
            || !PureConversion(method, narrowView)) return false;
        return ReferenceEquals(checkedSource, storedSource);
    }

    private static bool AddressTaken(IOperand operand, LocalVariable value) => operand switch
    {
        AddressOf address => ForwardNullCheckRecovery.Uses(address.Target, value),
        MemoryOperand memory => memory.Base != null && AddressTaken(memory.Base, value)
            || memory.Index != null && AddressTaken(memory.Index, value),
        ArrayAccess array => AddressTaken(array.Index, value),
        FieldReference field => field.Parent != null && AddressTaken(field.Parent, value),
        _ => false,
    };
}
