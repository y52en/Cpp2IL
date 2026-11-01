using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// The reviewed whole-image profile authenticates this complete memset PLT
// and its unique import relocation (2375/3041). Complete caller C3042 shows
// full zeroing of an ordinary local before its constructor/unmarshal/copy.
// Preserve all surrounding calls, guards, transfers and exception effects.
public static class NativeLocalZeroInitializationRecovery
{
    private const ulong Zero = 0xA5FF10;

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph) return 0;
        var calls = graph.Instructions.Where(i => i is
            { OpCode: OpCode.Call, Operands: [Immediate { UnsignedValue: Zero }, ..] }).ToArray();
        if (calls.Length == 0 || !CheckedUnboxRecovery.Supports(method.AppContext)) return 0;
        var count = calls.Count(call => TryRewrite(method, call, true));
        if (count > 0) DeadCodeEliminator.Run(method);
        return count;
    }

    internal static bool TryRewrite(MethodAnalysisContext method, Instruction call, bool reviewedImage)
    {
        if (!reviewedImage || method.ControlFlowGraph is not { } graph
            || call is not { OpCode: OpCode.Call, NativeVirtualDispatch: false,
                Operands: [Immediate { UnsignedValue: Zero }, LocalVariable result,
                    AddressOf { Target: LocalVariable local }, Immediate { Value: 0 }, Immediate bytes, ..] }
            || call.Operands.Skip(5).Any(o => o is not (LocalVariable or Immediate))
            || !method.Locals.Contains(local) || ReferenceEquals(local, result)
            || local.IsThis || local.IsReturn || local.IsReturnBuffer || local.IsMethodInfo
            || local.ParameterIndex >= 0 || method.ParameterLocals.Contains(local)
            || local.Type is not { IsValueType: true } type
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
        // AddressOf(local) denotes the same non-null local storage that initobj
        // updates. No pointer/type inference, partial zeroing or return-buffer
        // substitution is performed, and the unused native pointer result dies.
        call.OpCode = OpCode.Move;
        call.SetOperands(local, new DefaultStructValue(type));
        call.ImplicitDefinition = null;
        call.NativeReadSize = call.NativeWriteSize = 0;
        call.NativeZeroSize = (int)size;
        owners[0].CalculateBlockType();
        return true;
    }
}
