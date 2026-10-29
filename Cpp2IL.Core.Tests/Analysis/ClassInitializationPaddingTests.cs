using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClassInitializationPaddingTests
{
    [TestCase("valid",true)]
    [TestCase("single-padding",true)]
    [TestCase("constant-class",true)]
    [TestCase("minimal",false)]
    [TestCase("missing-class",false)]
    [TestCase("foreign-image",false)]
    [TestCase("foreign-address",false)]
    [TestCase("named-only",false)]
    [TestCase("void",false)]
    [TestCase("virtual",false)]
    [TestCase("invalid-result",false)]
    [TestCase("memory-padding",false)]
    [TestCase("address-padding",false)]
    [TestCase("float-padding",false)]
    [TestCase("string-padding",false)]
    public void KeepsClassArgumentReturnAndOpaqueEffects(string shape,bool expected)
    {
        LocalVariable Local(string name)=>new(name,new(null,name));
        var result=Local("result");var klass=Local("dynamic-class");
        List<IOperand> operands=[new Immediate(0xA79900),result,klass,Local("unused-x1"),new Immediate(11),Local("unused-v0")];
        if(shape=="single-padding")operands=operands.Take(4).ToList();
        if(shape=="constant-class")operands[2]=new Immediate(0x123456);
        if(shape=="minimal")operands=operands.Take(3).ToList();
        if(shape=="missing-class")operands=operands.Take(2).ToList();
        if(shape=="foreign-address")operands[0]=new Immediate(0xA79904);
        if(shape=="named-only")operands[0]=new StringLiteral("runtime_class_init");
        if(shape=="invalid-result")operands[1]=new Immediate(0);
        if(shape=="memory-padding")operands[3]=new MemoryOperand(klass);
        if(shape=="address-padding")operands[3]=new AddressOf(klass);
        if(shape=="float-padding")operands[3]=new FloatLiteral(1f);
        if(shape=="string-padding")operands[3]=new StringLiteral("effect");
        var call=new Instruction(7,shape=="void"?OpCode.CallVoid:OpCode.Call,operands){NativeVirtualDispatch=shape=="virtual"};
        var original=call.Operands.ToArray();var opcode=call.OpCode;
        Assert.That(RuntimeHelperArgumentPaddingRecovery.TryTrimClassInitialization(call,shape!="foreign-image"),Is.EqualTo(expected));
        Assert.That(call.Operands,Is.EqualTo(expected?original[..3]:original));
        Assert.That(call.OpCode,Is.EqualTo(opcode));
        Assert.That(klass.Type,Is.Null,"Dynamic metadata must remain dynamic");
        if(expected)
            Assert.That(RuntimeHelperArgumentPaddingRecovery.TryTrimClassInitialization(call,true),Is.False,"Trimming is idempotent");
    }
}
