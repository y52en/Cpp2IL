using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceDeadPhiTests
{
    private static LocalVariable V(string name)=>new(name,new Register(null,name));

    [Test]
    public void DeadPhiOnlyCycleIsProvedWithoutMutation()
    {
        var a=V("a");var b=V("b");var outside=V("outside");
        var first=new Instruction(0,OpCode.Phi,a,b,outside);
        var second=new Instruction(1,OpCode.Phi,b,a,a);
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([first,second],[first],out var removable),Is.True);
        Assert.That(removable,Is.EquivalentTo(new[]{first,second}));
        Assert.That(first.OpCode,Is.EqualTo(OpCode.Phi));
    }

    [TestCase("return")]
    [TestCase("store")]
    [TestCase("array")]
    [TestCase("length")]
    [TestCase("field")]
    [TestCase("address")]
    [TestCase("call")]
    public void EveryRealNestedUseRefusesEntireClosure(string kind)
    {
        var a=V("a");var b=V("b");var array=V("array");
        var first=new Instruction(0,OpCode.Phi,a,new Immediate(0),new Immediate(1));
        var second=new Instruction(1,OpCode.Phi,b,a,a);
        IOperand used=kind switch
        {
            "array"=>new ArrayAccess(array,b),
            "length"=>new ArrayLength(b),
            "field"=>new FieldReference(null!,b,0),
            "address"=>new AddressOf(new MemoryOperand(b)),
            _=>b
        };
        var consumer=kind switch
        {
            "store"=>new Instruction(2,OpCode.Move,new MemoryOperand(b),new Immediate(0)),
            "call"=>new Instruction(2,OpCode.CallVoid,new Immediate(123),b),
            _=>new Instruction(2,OpCode.Return,used)
        };
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([first,second,consumer],[first],out var removable),Is.False);
        Assert.That(removable,Is.Empty);
        Assert.That(first.OpCode,Is.EqualTo(OpCode.Phi));
    }

    [Test]
    public void AmbiguousSsaDestinationIsNotProvedDead()
    {
        var a=V("a");var first=new Instruction(0,OpCode.Phi,a,new Immediate(0),new Immediate(1));
        var duplicate=new Instruction(1,OpCode.Move,a,new Immediate(3));
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([first,duplicate],[first],out var removable),Is.False);
        Assert.That(removable,Is.Empty);
    }
}
