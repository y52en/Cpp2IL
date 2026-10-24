using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class MessageBuilderPaddingTests
{
    [TestCase("valid",true)]
    [TestCase("no-fingerprint",false)]
    [TestCase("foreign-image",false)]
    [TestCase("virtual",false)]
    [TestCase("callvoid",false)]
    [TestCase("unknown-label",false)]
    [TestCase("memory-tail",false)]
    [TestCase("address-tail",false)]
    public void OnlyFingerprintProvenOpaqueAbiPaddingIsRemoved(string shape,bool expected)
    {
        LocalVariable Local(string name)=>new(name,new(null,name));
        IOperand target=shape=="unknown-label"?new StringLiteral("unknown"):new Immediate(0xAE3F00);
        var result=Local("native-result");var source=Local("source-name");var klass=Local("target-name");
        IOperand tail=shape switch {"memory-tail"=>new MemoryOperand(source),
            "address-tail"=>new AddressOf(source),_=>Local("unused-X2")};
        var call=new Instruction(3,shape=="callvoid"?OpCode.CallVoid:OpCode.Call,target,result,source,klass,tail)
            {NativeVirtualDispatch=shape=="virtual"};
        var before=call.Operands.ToArray();var opcode=call.OpCode;
        Assert.That(RuntimeHelperArgumentPaddingRecovery.TryTrim(call,
            shape!="foreign-image",shape!="no-fingerprint"),Is.EqualTo(expected));
        Assert.That(call.Operands,Is.EqualTo(expected?before[..4]:before));
        Assert.That(call.OpCode,Is.EqualTo(opcode));
        Assert.That(call.Operands[0],Is.SameAs(target));
        Assert.That(call.Operands[2],Is.SameAs(source));
        Assert.That(call.Operands[3],Is.SameAs(klass));
    }
}
