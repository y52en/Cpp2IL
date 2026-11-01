using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class ControlFlowPhiEdgesTests
{
    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    public void RemoveEdgeKeepsPhiSourcesAligned(int removed)
    {
        var graph=new ISILControlFlowGraph([]);
        var incoming=new[]{new Block(),new Block(),new Block()};
        var join=new Block();
        var phi=new Instruction(0,OpCode.Phi,new Register(null,"dest"),
            new Immediate{Value=11},new Immediate{Value=22},new Immediate{Value=33});
        join.Instructions.Add(phi);
        foreach(var block in incoming){join.Predecessors.Add(block);block.Successors.Add(join);}
        graph.RemoveEdge(incoming[removed],join);
        Assert.That(join.Predecessors.Count,Is.EqualTo(2));
        Assert.That(phi.Operands.Count,Is.EqualTo(3));
        var expected=new List<long>{11,22,33};expected.RemoveAt(removed);
        for(var i=0;i<2;i++) Assert.That(((Immediate)phi.Operands[i+1]).Value,Is.EqualTo(expected[i]));
        Assert.That(incoming[removed].Successors,Is.Empty);
    }

    [Test]
    public void UnreachablePredecessorDoesNotContributeToLivePhi()
    {
        var graph=new ISILControlFlowGraph([]);
        var dead=new Block();
        var live=new Block();
        graph.Blocks.AddRange([dead,live]);
        graph.EntryBlock.Successors.Add(live);live.Predecessors.Add(graph.EntryBlock);
        dead.Successors.Add(live);live.Predecessors.Add(dead);
        var phi=new Instruction(0,OpCode.Phi,new Register(null,"dest"),
            new Immediate{Value=7},new Immediate{Value=99});
        live.Instructions.Add(phi);
        graph.RemoveUnreachableBlocks();
        Assert.That(graph.Blocks.Contains(dead),Is.False);
        Assert.That(live.Predecessors,Is.EqualTo(new[]{graph.EntryBlock}));
        Assert.That(phi.Operands.Count,Is.EqualTo(2));
        Assert.That(((Immediate)phi.Operands[1]).Value,Is.EqualTo(7));
    }

    [Test]
    public void BrokenPhiAlignmentIsRejectedInsteadOfSilentlyReassociated()
    {
        var graph=new ISILControlFlowGraph([]);
        var source=new Block();var join=new Block();
        source.Successors.Add(join);join.Predecessors.Add(source);
        join.Instructions.Add(new(0,OpCode.Phi,new Register(null,"dest")));
        Assert.Throws<System.InvalidOperationException>(()=>graph.RemoveEdge(source,join));
        Assert.That(join.Predecessors,Is.EqualTo(new[]{source}));
    }
}
