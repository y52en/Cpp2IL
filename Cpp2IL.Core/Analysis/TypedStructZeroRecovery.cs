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
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable { Type: { } type }, var source] }
                || !type.IsValueType || type.HasAnyGenericParameters() || TypeSizes.IsScalarValueType(type))continue;
            if(source is DefaultStructValue initialized && TrivialConstructorRecovery.SameType(initialized.Type,type))continue;
            if(source is not (Immediate {Value:0} or LocalVariable or DefaultStructValue))continue;
            var size=type is GenericInstanceTypeAnalysisContext
                ? ClosedGenericValueLayout.TryGet(type,method.AppContext.Binary.PointerSizeBytes)?.Size??0
                : TypeSizes.UnboxedSize(type,method.AppContext.Binary.PointerSizeBytes);
            if(size is <=0 or >256)continue;
            // NativeZeroSize is an independently checked original byte union,
            // recorded before SSA/typing can turn a shared zero register into
            // one particular aggregate. A partial vector store can therefore
            // initialize a DIFFERENT full aggregate without copying that
            // register's inferred managed type. Width alone only proves an
            // immediate zero; an arbitrary local needs the full zero proof.
            if(instruction.NativeZeroSize<size
                && (source is not Immediate {Value:0} || instruction.NativeWriteSize!=size))continue;
            instruction.SetOperand(1, new DefaultStructValue(type));
            count++;
        }
        return count;
    }
}
