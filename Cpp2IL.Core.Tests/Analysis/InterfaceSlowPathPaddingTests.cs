using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceSlowPathPaddingTests
{
    [TestCase("valid",true)]
    [TestCase("minimal",false)]
    [TestCase("missing-slot",false)]
    [TestCase("foreign-image",false)]
    [TestCase("foreign-address",false)]
    [TestCase("named-only",false)]
    [TestCase("void",false)]
    [TestCase("virtual",false)]
    [TestCase("invalid-result",false)]
    [TestCase("memory-padding",false)]
    [TestCase("address-padding",false)]
    [TestCase("float-padding",false)]
    public void RetainsOpaqueCallAndActualThreeInputs(string shape,bool expected)
    {
        LocalVariable Local(string name)=>new(name,new(null,name));
        var result=Local("result");var receiver=Local("object");var owner=Local("dynamic-interface");var slot=Local("slot");
        List<IOperand> operands=[new Immediate(0xA7A4D0),result,receiver,owner,slot,Local("unused-x3"),Local("unused-v0")];
        if(shape=="minimal")operands=operands.Take(5).ToList();
        if(shape=="missing-slot")operands=operands.Take(4).ToList();
        if(shape=="foreign-address")operands[0]=new Immediate(0xA7A348);
        if(shape=="named-only")operands[0]=new StringLiteral("GetInterfaceInvokeDataFromVTableSlowPath");
        if(shape=="invalid-result")operands[1]=new Immediate(0);
        if(shape=="memory-padding")operands[5]=new MemoryOperand(receiver);
        if(shape=="address-padding")operands[5]=new AddressOf(receiver);
        if(shape=="float-padding")operands[5]=new FloatLiteral(1f);
        var call=new Instruction(7,shape=="void"?OpCode.CallVoid:OpCode.Call,operands){NativeVirtualDispatch=shape=="virtual"};
        var original=call.Operands.ToArray();var opcode=call.OpCode;
        Assert.That(RuntimeHelperArgumentPaddingRecovery.TryTrimInterfaceSlowPath(call,shape!="foreign-image"),Is.EqualTo(expected));
        Assert.That(call.Operands,Is.EqualTo(expected?original[..5]:original));
        Assert.That(call.OpCode,Is.EqualTo(opcode));
        Assert.That(owner.Type,Is.Null,"No guessed interface token or managed call may be synthesized");
    }
}
