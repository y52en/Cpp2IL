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
        var calls=graph.Instructions.Where(i=>i.OpCode==OpCode.Call&&i.Operands.Count>3).ToArray();
        if(calls.Length==0||!CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        return calls.Count(call=>TryTrimClassInitialization(call,true) || TryTrimInterfaceSlowPath(call,true) || TryTrim(call,true,
            call.Operands[0] is Immediate {Value:>=0} address
                && InlineClassCastRecovery.IsMessageBuilder(method,(ulong)address.Value)));
    }

    // Complete primary C for 0xA79900 and its 0xA7749C callee proves a
    // single incoming class pointer. The latter overwrites X1 before passing
    // its local synchronization state onward. No incoming X1-X7/SIMD value
    // is an argument. Retain the opaque call, return and actual class operand,
    // including initialization/exception effects; do not manufacture managed IL.
    // Production reaches this only under the full relocated image hash above.
    internal static bool TryTrimClassInitialization(Instruction call,bool reviewedImage)
    {
        if(!reviewedImage || call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,
                Operands:[Immediate {Value:0xA79900},LocalVariable,_,..]}
            || call.Operands.Count<=3
            || call.Operands.Skip(3).Any(o=>o is not (LocalVariable or Immediate)))return false;
        call.SetOperands(call.Operands.Take(3).ToList());
        return true;
    }

    // Complete original helper C and 708-byte FDE: object, interface, slot in
    // X0/X1/W2; no incoming X3-X7 or SIMD arguments. Whole-image Supports above
    // authenticates this RVA and body, including all C++ cleanup landing pads.
    // Keep the opaque call, result, all three real inputs and exception effects.
    internal static bool TryTrimInterfaceSlowPath(Instruction call,bool reviewedImage)
    {
        if(!reviewedImage || call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,
                Operands:[Immediate {Value:0xA7A4D0},LocalVariable,_,_,_,..]}
            || call.Operands.Count<=5
            || call.Operands.Skip(5).Any(o=>o is not (LocalVariable or Immediate)))return false;
        call.SetOperands(call.Operands.Take(5).ToList());
        return true;
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
