using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceLookupEntryTests
{
    [TestCase("shared-klass",true)]
    [TestCase("old-entry",true)]
    [TestCase("callback",false)]
    [TestCase("escape",false)]
    [TestCase("external-entry",false)]
    [TestCase("foreign-exit",false)]
    public void SelectsOnlyAClosedPureLookupWhileRetainingBusinessBranch(string shape,bool expected)
    {
        var cfg=new ISILControlFlowGraph([]);
        var klassHead=new Block{ID=2};var entry=new Block{ID=3};var fast=new Block{ID=4};
        var slow=new Block{ID=5};var merge=new Block{ID=6};var business=new Block{ID=7};
        cfg.Blocks.AddRange([klassHead,entry,fast,slow,merge,business]);
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(cfg.EntryBlock,klassHead);Edge(klassHead,entry);Edge(entry,fast);Edge(entry,slow);
        Edge(fast,merge);Edge(slow,merge);Edge(merge,cfg.ExitBlock);
        if(shape!="old-entry"){Edge(klassHead,business);Edge(business,cfg.ExitBlock);}
        if(shape=="external-entry")Edge(business,slow);
        if(shape=="foreign-exit")Edge(fast,business);
        var flag=new LocalVariable("flag",new Register(null,"flag"));
        var value=new LocalVariable("value",new Register(null,"value"));
        var result=new LocalVariable("result",new Register(null,"result"));
        klassHead.Instructions=[new(0,OpCode.CallVoid,new StringLiteral("source callback")),new(1,OpCode.ConditionalJump,business,flag)];
        if(shape=="old-entry")klassHead.Instructions[^1]=new(1,OpCode.Jump,entry);
        entry.Instructions=[new(2,OpCode.ConditionalJump,fast,flag)];
        fast.Instructions=[new(3,OpCode.Add,value,new Immediate(1),new Immediate(2)),new(4,OpCode.Jump,merge)];
        var slowCall=new Instruction(5,OpCode.Call,new Immediate(0x1234),result);
        slow.Instructions=[slowCall,new(6,OpCode.Jump,merge)];
        merge.Instructions=[new(7,OpCode.Return)];business.Instructions=[new(8,OpCode.CallVoid,new StringLiteral("other callback")),new(9,OpCode.Return)];
        if(shape=="callback")fast.Instructions.Insert(0,new(10,OpCode.CallVoid,new StringLiteral("must retain")));
        if(shape=="escape")merge.Instructions[0]=new(7,OpCode.Return,value);
        var originalInstructions=cfg.Blocks.SelectMany(b=>b.Instructions).ToArray();
        var originalSuccessors=klassHead.Successors.ToArray();
        Assert.That(InterfaceDispatchRecovery.TryFindLookupRegion(cfg,klassHead,merge,slowCall,out var head,out var region),Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(head,Is.SameAs(shape=="old-entry"?klassHead:entry));
            Assert.That(region.Contains(fast) && region.Contains(slow),Is.True);
            Assert.That(region.Contains(business),Is.False);
        }
        // Finding a cut is a pure proof operation: no speculative CFG edits.
        Assert.That(klassHead.Successors,Is.EqualTo(originalSuccessors));
        Assert.That(cfg.Blocks.SelectMany(b=>b.Instructions),Is.EqualTo(originalInstructions));
    }
}
