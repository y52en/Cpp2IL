using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Metadata may identify an address-taken stack value only after the initial
// native stack pass. Preserve its full-width zero as mutable struct storage
// BEFORE SSA forwarding can substitute scalar zero into its later reads.
public static class TypedStructZeroRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        var count = 0;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable { Type: { } type }, Immediate { Value: 0 }] }
                || !type.IsValueType || type.HasAnyGenericParameters() || TypeSizes.IsScalarValueType(type))continue;
            var size=type is GenericInstanceTypeAnalysisContext
                ? ClosedGenericValueLayout.TryGet(type,method.AppContext.Binary.PointerSizeBytes)?.Size??0
                : TypeSizes.UnboxedSize(type,method.AppContext.Binary.PointerSizeBytes);
            if(size is <=0 or >256 || instruction.NativeWriteSize!=size && instruction.NativeZeroSize<size)continue;
            instruction.SetOperand(1, new DefaultStructValue(type));
            count++;
        }
        return count;
    }
}
