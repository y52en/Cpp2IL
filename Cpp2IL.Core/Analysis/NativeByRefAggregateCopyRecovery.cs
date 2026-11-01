using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Complete primary3030/3042 and import audit2375 identify this memcpy PLT.
// Only a complete value copy into an actual metadata-bound ref/out parameter
// is recovered. Unknown scratch storage and partial copies remain opaque.
public static class NativeByRefAggregateCopyRecovery
{
    private const ulong Copy = 0xA5FC30;
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph) return 0;
        var calls = graph.Instructions.Where(i => i is
            { OpCode: OpCode.Call, Operands: [Immediate { UnsignedValue: Copy }, ..] }).ToArray();
        if (calls.Length == 0 || !CheckedUnboxRecovery.Supports(method.AppContext)) return 0;
        var count = calls.Count(call => TryRewrite(method, call, true));
        if (count > 0) DeadCodeEliminator.Run(method);
        return count;
    }

    internal static bool TryRewrite(MethodAnalysisContext method, Instruction call, bool reviewedImage)
    {
        if (!reviewedImage || method.ControlFlowGraph is not { } graph
            || call is not { OpCode: OpCode.Call, NativeVirtualDispatch: false,
                Operands: [Immediate { UnsignedValue: Copy }, LocalVariable result,
                    LocalVariable { Type: ByRefTypeAnalysisContext reference } destination,
                    AddressOf { Target: LocalVariable source }, Immediate bytes, ..] }
            || call.Operands.Skip(5).Any(o => o is not (LocalVariable or Immediate))
            || !method.Locals.Contains(destination) || !method.ParameterLocals.Contains(destination)
            || destination.IsThis || destination.IsMethodInfo || destination.IsReturnBuffer
            || destination.ParameterIndex < 0 || destination.ParameterIndex >= method.Parameters.Count
            || method.Parameters[destination.ParameterIndex].ParameterType is not ByRefTypeAnalysisContext original
            || !TrivialConstructorRecovery.SameType(original.ElementType, reference.ElementType)
            || !method.Locals.Contains(source) || source.IsThis || source.IsReturnBuffer
            || ReferenceEquals(source, result) || ReferenceEquals(destination, result)
            || source.Type is not { IsValueType: true } type
            || !TrivialConstructorRecovery.SameType(reference.ElementType, type)
            || TypeSizes.IsScalarValueType(type) || type.HasAnyGenericParameters()) return false;
        var size = type is GenericInstanceTypeAnalysisContext
            ? ClosedGenericValueLayout.TryGet(type, method.AppContext.Binary.PointerSizeBytes)?.Size ?? 0
            : TypeSizes.UnboxedSize(type, method.AppContext.Binary.PointerSizeBytes);
        if (size is <= 0 or > 4096 || bytes.Value != size) return false;
        var instructions = graph.Instructions.ToArray();
        var owners = graph.Blocks.Where(b => b.Instructions.Contains(call)).ToArray();
        if (owners.Length != 1 || instructions.Count(i => ReferenceEquals(i.Destination, result)) != 1
            || instructions.Any(i => !ReferenceEquals(i, call)
                && InterfaceDispatchRecovery.UsedLocals(i).Contains(result))) return false;
        // MemoryOperand(refParameter) is emitted by the existing stobj path.
        // Assigning to the LocalVariable itself would replace its pointer.
        call.OpCode = OpCode.Move;
        call.SetOperands(new MemoryOperand(destination), source);
        call.ImplicitDefinition = null;
        call.NativeReadSize = call.NativeWriteSize = call.NativeZeroSize = 0;
        owners[0].CalculateBlockType();
        return true;
    }
}
