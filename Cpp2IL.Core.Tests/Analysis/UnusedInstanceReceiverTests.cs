using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class UnusedInstanceReceiverTests
{
    private static Register X(int n)=>new(null,"X"+n);
    private static bool Unused(params Instruction[] instructions)=>UnusedInstanceReceiverRecovery.EntryX0Unused(new ISILControlFlowGraph(new List<Instruction>(instructions)));

    [Test]
    public void EntryX0OverwrittenBeforeStaticForwardingIsUnused()
    {
        Assert.That(Unused(new(0,OpCode.Move,X(19),X(1)),new(1,OpCode.Move,X(0),new Immediate(42)),
            new(2,OpCode.CallVoid,new Immediate(0x1000),X(0)),new(3,OpCode.Return)),Is.True);
    }

    [TestCase("copy")]
    [TestCase("load")]
    [TestCase("store_base")]
    [TestCase("call")]
    [TestCase("indirect_target")]
    [TestCase("return")]
    [TestCase("self_update")]
    public void EveryReadBeforeKillIncludingMemoryDestinationRejects(string shape)
    {
        var use=shape switch
        {
            "copy"=>new Instruction(0,OpCode.Move,X(19),X(0)),
            "load"=>new Instruction(0,OpCode.Move,X(1),new MemoryOperand(X(0))),
            "store_base"=>new Instruction(0,OpCode.Move,new MemoryOperand(X(0)),new Immediate(1)),
            "call"=>new Instruction(0,OpCode.CallVoid,new Immediate(0x1000),X(0)),
            "indirect_target"=>new Instruction(0,OpCode.IndirectCall,X(0),X(1)),
            "return"=>new Instruction(0,OpCode.Return,X(0)),
            _=>new Instruction(0,OpCode.Add,X(0),X(0),new Immediate(1))
        };
        Assert.That(Unused(use,new(1,OpCode.Return)),Is.False);
    }

    [Test]
    public void UnknownInstructionWhileEntryReceiverIsLiveRejects()
    {
        Assert.That(Unused(new(0,OpCode.Invalid,new StringLiteral("unknown")),new(1,OpCode.Return)),Is.False);
    }

    [Test]
    public void OneBranchReadingReceiverCannotBeHiddenByOtherBranchKill()
    {
        var use=new Instruction(4,OpCode.Move,X(19),X(0));
        Assert.That(Unused(new(0,OpCode.ConditionalJump,use,new Immediate(1)),
            new(1,OpCode.Move,X(0),new Immediate(0)),new(2,OpCode.Return),use,new(5,OpCode.Return)),Is.False);
    }
}
