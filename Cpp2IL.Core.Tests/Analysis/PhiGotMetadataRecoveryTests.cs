using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class PhiGotMetadataRecoveryTests
{
    [TestCase("same-slot",true)]
    [TestCase("equivalent-slots",true)]
    [TestCase("anchored-loop",true)]
    [TestCase("copy",true)]
    [TestCase("different-address",false)]
    [TestCase("not-got",false)]
    [TestCase("partial-read",false)]
    [TestCase("partial-use",false)]
    [TestCase("partial-copy",false)]
    [TestCase("unknown-incoming",false)]
    [TestCase("unanchored-loop",false)]
    [TestCase("separate-unanchored-cycle",false)]
    [TestCase("offset-use",false)]
    [TestCase("indexed-use",false)]
    [TestCase("before-definition",false)]
    [TestCase("ambiguous-definition",false)]
    [TestCase("implicit-clobber",false)]
    [TestCase("excessive-chain",false)]
    public void EveryIncomingPointerAndCycleNeedsTheSameRealGotAnchor(string shape,bool expected)
    {
        LocalVariable V(string name)=>new(name,new Register(null,name));
        var one=V("one");var two=V("two");var root=V("root");var copy=V("copy");var unknown=V("unknown");var cycle=V("cycle");
        var first=new Instruction(0,OpCode.Move,one,new MemoryOperand(addend:0x1000)){NativeReadSize=8};
        var second=new Instruction(1,OpCode.Move,two,new MemoryOperand(addend:shape=="equivalent-slots" || shape=="different-address"?0x1100:0x1000)){NativeReadSize=shape=="partial-read"?4:8};
        var phi=new Instruction(2,OpCode.Phi,root,one,two);
        var use=new Instruction(4,OpCode.Move,V("value"),new MemoryOperand(root)){NativeReadSize=shape=="partial-use"?4:8};
        var list=new List<Instruction>{first,second,phi,use,new(5,OpCode.Return)};
        if(shape=="anchored-loop")phi.SetOperand(2,root);
        if(shape=="unknown-incoming")phi.SetOperand(2,unknown);
        if(shape=="unanchored-loop")phi.SetOperands(root,root);
        if(shape=="separate-unanchored-cycle")
        {list.Insert(2,new(6,OpCode.Phi,cycle,cycle));phi.SetOperand(2,cycle);}
        if(shape is "copy" or "partial-copy")
        {list.Insert(3,new(3,OpCode.Move,copy,root){NativeRegisterCopySize=shape=="partial-copy"?4:8});use.SetOperand(1,new MemoryOperand(copy));}
        if(shape=="offset-use")use.SetOperand(1,new MemoryOperand(root,addend:8));
        if(shape=="indexed-use")use.SetOperand(1,new MemoryOperand(root,root,scale:8));
        if(shape=="before-definition"){list.Remove(use);list.Insert(0,use);}
        if(shape=="ambiguous-definition")list.Insert(3,new(7,OpCode.Move,root,one));
        if(shape=="implicit-clobber")list.Insert(3,new(7,OpCode.CallVoid,new StringLiteral("callback")){ImplicitDefinition=one.Register});
        if(shape=="excessive-chain")
        {
            var previous=root;
            for(var n=0;n<270;n++)
            {var next=V("chain"+n);list.Insert(list.Count-2,new(10+n,OpCode.Move,next,previous){NativeRegisterCopySize=8});previous=next;}
            use.SetOperand(1,new MemoryOperand(previous));
        }
        var graph=new ISILControlFlowGraph(list);
        var definitions=graph.Instructions.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var before=graph.Instructions.ToArray();
        var address=MetadataResolver.PhiGotMetadataAddress(use,graph,definitions,8,
            slot=>shape=="not-got"?null:slot==0x1000?0x2000UL:slot==0x1100?(shape=="different-address"?0x3000UL:0x2000UL):null);
        Assert.That(address,Is.EqualTo(expected?0x2000UL:(ulong?)null));
        Assert.That(graph.Instructions,Is.EqualTo(before));
    }
}
