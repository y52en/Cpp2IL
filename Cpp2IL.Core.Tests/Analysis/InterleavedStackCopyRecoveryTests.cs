using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterleavedStackCopyRecoveryTests
{
    private static Register R(string name)=>new(null,name);
    internal static Instruction[] Copy()=>[
        new(0,OpCode.Move,R("X8"),R("stack_-A8")){NativeReadSize=8},
        new(1,OpCode.Move,R("V0"),R("stack_-B8")){NativeReadSize=16},
        new(2,OpCode.Move,R("stack_-70"),R("X8")){NativeWriteSize=8},
        new(3,OpCode.Move,R("stack_-80"),R("V0")){NativeWriteSize=16},
        new(4,OpCode.Move,R("V0"),R("stack_-C8")){NativeReadSize=16},
        new(5,OpCode.Move,R("stack_-90"),R("V0")){NativeWriteSize=16},
        new(6,OpCode.Return)];

    [Test]
    public void FullDisjointCopyAllowsLaterSourceLoadsWithoutChangingTheirValues()
    {
        var instructions=Copy();var graph=new ISILControlFlowGraph(instructions.ToList());
        var block=graph.Blocks.Single(b=>b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph,block,0,R("stack_-C8"),40),Is.True);
        Assert.That(instructions[2].Operands[0],Is.EqualTo(R("stack_-90")));
        Assert.That(instructions[2].Operands[1],Is.EqualTo(R("stack_-C8")));
        Assert.That(instructions[4].OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(instructions[4].NativeReadSize,Is.EqualTo(16));
        Assert.That(instructions[3].OpCode,Is.EqualTo(OpCode.Nop));
        Assert.That(instructions[5].OpCode,Is.EqualTo(OpCode.Nop));
    }

    [TestCase("destination-observer")]
    [TestCase("unknown-read")]
    [TestCase("unapproved-global")]
    [TestCase("call")]
    [TestCase("source-write")]
    public void PartialDestinationObserversOrUnprovedEffectsRemainUnchanged(string shape)
    {
        var instructions=Copy().ToList();
        var extra=shape switch {
            "destination-observer"=>new Instruction(7,OpCode.Move,R("X22"),R("stack_-88")){NativeReadSize=8},
            "unknown-read"=>new Instruction(7,OpCode.Move,R("X22"),new MemoryOperand(R("X4"))){NativeReadSize=8},
            "unapproved-global"=>new Instruction(7,OpCode.Move,R("X22"),new MemoryOperand(addend:0x1234)){NativeReadSize=8},
            "call"=>new Instruction(7,OpCode.CallVoid,new Immediate(0x1234)),
            _=>new Instruction(7,OpCode.Move,R("stack_-C8"),R("X0")){NativeWriteSize=8}};
        instructions.Insert(4,extra);
        var before=instructions.Select(i=>(i.ToString(),i.NativeReadSize,i.NativeWriteSize)).ToArray();
        var graph=new ISILControlFlowGraph(instructions);
        var block=graph.Blocks.Single(b=>b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph,block,0,R("stack_-C8"),40),Is.False);
        Assert.That(instructions.Select(i=>(i.ToString(),i.NativeReadSize,i.NativeWriteSize)),Is.EqualTo(before));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void OnlyExplicitlyApprovedGotReadsCanInterleaveAfterPartialStores(bool approved)
    {
        var instructions=Copy().ToList();
        var metadata=new Instruction(7,OpCode.Move,R("X22"),new MemoryOperand(addend:0x1234)){NativeReadSize=8};
        instructions.Insert(5,metadata);
        var before=instructions.Select(i=>(i.ToString(),i.NativeReadSize,i.NativeWriteSize)).ToArray();
        var graph=new ISILControlFlowGraph(instructions);
        var block=graph.Blocks.Single(b=>b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph,block,0,R("stack_-C8"),40,
            slot=>approved&&slot==0x1234),Is.EqualTo(approved));
        Assert.That(metadata.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(metadata.NativeReadSize,Is.EqualTo(8));
        if(!approved)Assert.That(instructions.Select(i=>(i.ToString(),i.NativeReadSize,i.NativeWriteSize)),Is.EqualTo(before));
    }
}
