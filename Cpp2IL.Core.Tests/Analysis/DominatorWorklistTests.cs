using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Tests.Analysis;

public class DominatorWorklistTests
{
    private static ISILControlFlowGraph Graph(int[][] successors)
    {
        var graph=new ISILControlFlowGraph([]);
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock]; // Empty constructor also creates a synthetic body block.
        for(var n=2;n<successors.Length;n++)graph.Blocks.Add(new Block{ID=n});
        var nodes=graph.Blocks.ToArray();
        foreach(var block in nodes){block.Successors.Clear();block.Predecessors.Clear();}
        for(var n=0;n<nodes.Length;n++)foreach(var next in successors[n])
        {nodes[n].Successors.Add(nodes[next]);nodes[next].Predecessors.Add(nodes[n]);}
        return graph;
    }

    // Independent definition: d dominates n exactly when deleting d makes n
    // unreachable from entry. No dominator/intersection algorithm is reused.
    private static HashSet<Block> Reach(ISILControlFlowGraph graph,Block? removed=null)
    {
        var seen=new HashSet<Block>();var pending=new Stack<Block>();
        if(!ReferenceEquals(removed,graph.EntryBlock))pending.Push(graph.EntryBlock);
        while(pending.TryPop(out var block))
            if(seen.Add(block))foreach(var next in block.Successors)
                if(!ReferenceEquals(next,removed))pending.Push(next);
        return seen;
    }

    private static void Verify(ISILControlFlowGraph graph)
    {
        Assert.That(Reach(graph).Count,Is.EqualTo(graph.Blocks.Count));
        var removed=graph.Blocks.ToDictionary(b=>b,b=>Reach(graph,b));
        var expected=graph.Blocks.ToDictionary(b=>b,b=>graph.Blocks.Where(d=>!removed[d].Contains(b)).ToHashSet());
        var actual=new DominatorInfo(graph);
        foreach(var block in graph.Blocks)
        {
            Assert.That(actual.Dominators[block],Is.EquivalentTo(expected[block]));
            foreach(var d in graph.Blocks)Assert.That(actual.Dominates(d,block),Is.EqualTo(expected[block].Contains(d)));
            var strict=expected[block].Where(d=>!ReferenceEquals(d,block)).ToArray();
            var parent=strict.OrderByDescending(d=>expected[d].Count).FirstOrDefault();
            Assert.That(actual.ImmediateDominators[block],Is.SameAs(parent));
            var frontier=graph.Blocks.Where(y=>y.Predecessors.Any(p=>expected[p].Contains(block))
                && (ReferenceEquals(block,y)||!expected[y].Contains(block)));
            Assert.That(actual.DominanceFrontier[block],Is.EquivalentTo(frontier));
        }
    }

    [Test]
    public void EveryReachableFourBlockGraphMatchesPathDeletionDefinition()
    {
        var edges=(from a in new[]{0,2,3}from b in new[]{1,2,3}select(a,b)).ToArray();var checkedGraphs=0;
        for(var mask=0;mask<(1<<edges.Length);mask++)
        {
            var successors=Enumerable.Range(0,4).Select(_=>new List<int>()).ToArray();
            for(var n=0;n<edges.Length;n++)if((mask&(1<<n))!=0)successors[edges[n].a].Add(edges[n].b);
            var graph=Graph(successors.Select(s=>s.ToArray()).ToArray());
            if(Reach(graph).Count!=4)continue;
            Verify(graph);checkedGraphs++;
        }
        Assert.That(checkedGraphs,Is.EqualTo(224));
    }

    [TestCase(8)] [TestCase(20)] [TestCase(64)]
    public void SeededJoinsAndBackEdgesRetainDominatorsAndFrontiers(int count)
    {
        var random=new Random(2492+count);
        for(var attempt=0;attempt<30;attempt++)
        {
            var order=new[]{0}.Concat(Enumerable.Range(2,count-2)).Append(1).ToArray();
            var successors=Enumerable.Range(0,count).Select(_=>new HashSet<int>()).ToArray();
            for(var n=0;n<order.Length-1;n++)
            {
                successors[order[n]].Add(order[n+1]);
                for(var k=0;k<4;k++)successors[order[n]].Add(random.Next(1,count));
            }
            Verify(Graph(successors.Select(s=>s.OrderBy(x=>x).ToArray()).ToArray()));
        }
    }
}
