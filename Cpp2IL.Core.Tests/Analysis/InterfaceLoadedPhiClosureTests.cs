using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceLoadedPhiClosureTests
{
    private static LocalVariable V(string name)=>new(name,new Register(null,name));

    [TestCase(false)]
    [TestCase(true)]
    public void LoadedMetadataMayFeedOnlyADeadPhiClosure(bool cycle)
    {
        var pointer=V("pointer");var loaded=V("loaded");var first=V("first");var second=V("second");
        var root=new Instruction(0,OpCode.Phi,pointer,new Immediate(256),new Immediate(512));
        var load=new Instruction(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:8));
        var merge=new Instruction(2,OpCode.Phi,first,loaded,cycle?second:new Immediate(0));
        var tail=new Instruction(3,OpCode.Phi,second,first,new Immediate(1));
        var all=new[]{root,load,merge,tail};
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure(all,[root],out var removable),Is.True);
        Assert.That(removable,Is.EquivalentTo(all));
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(merge.OpCode,Is.EqualTo(OpCode.Phi));
    }

    [TestCase("return")]
    [TestCase("compare")]
    [TestCase("call")]
    [TestCase("store")]
    [TestCase("address")]
    [TestCase("load-again")]
    [TestCase("copy")]
    public void AnyRealOrUnprovedConsumerOfLoadedMetadataRefusesWholeClosure(string kind)
    {
        var pointer=V("pointer");var loaded=V("loaded");var merged=V("merged");var output=V("output");
        var root=new Instruction(0,OpCode.Phi,pointer,new Immediate(256),new Immediate(512));
        var load=new Instruction(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:8));
        var merge=new Instruction(2,OpCode.Phi,merged,loaded,new Immediate(0));
        var consumer=kind switch {
            "compare"=>new Instruction(3,OpCode.CheckNotEqual,output,loaded,new Immediate(0)),
            "call"=>new Instruction(3,OpCode.CallVoid,new Immediate(123),loaded),
            "store"=>new Instruction(3,OpCode.Move,new MemoryOperand(loaded),new Immediate(0)),
            "address"=>new Instruction(3,OpCode.Return,new AddressOf(loaded)),
            "load-again"=>new Instruction(3,OpCode.Move,output,new MemoryOperand(loaded)),
            "copy"=>new Instruction(3,OpCode.Move,output,loaded),
            _=>new Instruction(3,OpCode.Return,loaded)};
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([root,load,merge,consumer],[root],out var removable),Is.False);
        Assert.That(removable,Is.Empty);
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
    }

    [Test]
    public void ObservableUseBeyondLoadedPhiChainStillRefusesEntireClosure()
    {
        var pointer=V("pointer");var loaded=V("loaded");var merged=V("merged");
        var root=new Instruction(0,OpCode.Phi,pointer,new Immediate(256),new Immediate(512));
        var load=new Instruction(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:8));
        var merge=new Instruction(2,OpCode.Phi,merged,loaded,new Immediate(0));
        var observable=new Instruction(3,OpCode.Return,merged);
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([root,load,merge,observable],[root],out var removable),Is.False);
        Assert.That(removable,Is.Empty);
    }

    [Test]
    public void ReusedLoadedDestinationIsNotAnSsaProof()
    {
        var pointer=V("pointer");var loaded=V("loaded");var merged=V("merged");
        var root=new Instruction(0,OpCode.Phi,pointer,new Immediate(256),new Immediate(512));
        var load=new Instruction(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:8));
        var merge=new Instruction(2,OpCode.Phi,merged,loaded,new Immediate(0));
        var duplicate=new Instruction(3,OpCode.Move,loaded,new Immediate(7));
        Assert.That(InterfaceDispatchRecovery.DeadPhiClosure([root,load,merge,duplicate],[root],out var removable),Is.False);
        Assert.That(removable,Is.Empty);
    }
}
