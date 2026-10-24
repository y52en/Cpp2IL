using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Normalize only reviewed native ABI padding while SSA identities remain.
// Keep every actual argument, the opaque call, and the dynamic class operand.
// Interface lookup removal must still pass all original escape/effect proofs.
public static class RuntimeHelperArgumentPaddingRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var calls=graph.Instructions.Where(i=>i.OpCode==OpCode.Call&&i.Operands.Count>4).ToArray();
        if(calls.Length==0||!CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        return calls.Count(call=>TryTrim(call,true,
            call.Operands[0] is Immediate {Value:>=0} address
                && InlineClassCastRecovery.IsMessageBuilder(method,(ulong)address.Value)));
    }

    internal static bool TryTrim(Instruction call,bool reviewedImage,bool messageBuilderFingerprint=false)
    {
        if(!reviewedImage || call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,
                Operands:[var target,LocalVariable,_,_,..]} || call.Operands.Count<=4)return false;
        var known=target is StringLiteral {Value:"il2cpp_vm_object_is_inst" or "il2cpp_vm_object_box" or "il2cpp_value_box"}
            || target is Immediate {Value:0xA61E70}
            // Native string output is transported separately through X8. Keep
            // the opaque call/result and both X0/X1 inputs; only unused register
            // padding is removed. Never synthesize a managed call/return here.
            || messageBuilderFingerprint && target is Immediate {Value:>=0};
        if(!known||call.Operands.Skip(4).Any(o=>o is not (LocalVariable or Immediate)))return false;
        call.SetOperands(call.Operands.Take(4).ToList());
        return true;
    }
}
