using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class MetadataInitForkTests
{
    [TestCase("valid",true)]
    [TestCase("same-phi",true)]
    [TestCase("different-store",false)]
    [TestCase("wide-store",false)]
    [TestCase("wide-read",false)]
    [TestCase("wrong-value",false)]
    [TestCase("foreign-call",false)]
    [TestCase("additional-store",false)]
    [TestCase("effectful-plain",false)]
    [TestCase("different-business-condition",false)]
    [TestCase("different-business-arm",false)]
    [TestCase("external-entry",false)]
    [TestCase("escaping-value",false)]
    [TestCase("different-phi",false)]
    [TestCase("partial-phi",false)]
    [TestCase("unknown-address",false)]
    [TestCase("multiple-definition-address",false)]
    public void OnlyEquivalentBusinessForkAroundExactMetadataByteFlagCanBeRemoved(string shape,bool expected)
    {
        LocalVariable Local(string name)=>new(name,new(null,name));
        var graph=new ISILControlFlowGraph([]);
        var guard=new Block{ID=2};var plain=new Block{ID=3};var init=new Block{ID=4};
        var yes=new Block{ID=5};var no=new Block{ID=6};
        graph.Blocks.AddRange([guard,plain,init,yes,no]);
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,plain);Edge(guard,init);
        Edge(plain,yes);Edge(plain,no);Edge(init,yes);Edge(init,no);
        Edge(yes,graph.ExitBlock);Edge(no,graph.ExitBlock);
        var address=Local("address");var flag=Local("flag");var masked=Local("masked");var check=Local("check");
        var message=Local("message");var normal=Local("normal");var other=Local("other");
        var initCheck=Local("initCheck");var inverted=Local("inverted");var result=Local("result");var one=Local("one");
        guard.Instructions=[new(0,OpCode.Move,address,new Immediate(0x10000)),
            new(1,OpCode.Move,flag,new MemoryOperand(addend:0x10651)){NativeReadSize=shape=="wide-read"?4:1},
            new(2,OpCode.And,masked,flag,new Immediate(1)),new(3,OpCode.CheckEqual,check,masked,new Immediate(0)),
            new(4,OpCode.ConditionalJump,init,check)];
        plain.Instructions=[new(5,OpCode.CheckEqual,normal,message,new Immediate(0)),new(6,OpCode.ConditionalJump,yes,normal)];
        init.Instructions=[new(7,OpCode.Call,new StringLiteral("il2cpp_codegen_initialize_method"),result,new Immediate(11)),
            new(8,OpCode.Or,one,new Immediate(0),new Immediate(shape=="wrong-value"?2:1)),
            new(9,OpCode.Move,new MemoryOperand(address,addend:shape=="different-store"?0x652:0x651),one){NativeWriteSize=shape=="wide-store"?8:1},
            new(10,OpCode.CheckEqual,initCheck,shape=="different-business-condition"?other:message,new Immediate(0)),
            new(11,OpCode.Not,inverted,initCheck),new(12,OpCode.ConditionalJump,shape=="different-business-arm"?yes:no,inverted)];
        yes.Instructions=[new(13,OpCode.Return,message)];no.Instructions=[new(14,OpCode.Return)];
        if(shape=="foreign-call")init.Instructions[0].SetOperand(0,new StringLiteral("business callback"));
        if(shape=="additional-store")init.Instructions.Insert(1,new(15,OpCode.Move,new MemoryOperand(addend:0x9000),new Immediate(1)));
        if(shape=="effectful-plain")plain.Instructions.Insert(0,new(16,OpCode.CallVoid,new StringLiteral("keep")));
        if(shape=="external-entry")Edge(graph.EntryBlock,init);
        if(shape=="escaping-value")yes.Instructions[0].SetOperand(0,result);
        if(shape is "same-phi" or "different-phi" or "partial-phi")
        {
            var phi=new Instruction(-1,OpCode.Phi,Local("merged"),message,shape=="different-phi"?other:message);
            if(shape=="partial-phi")phi.RemoveOperandAt(2);
            yes.Instructions[0].SetOperand(0,phi.Operands[0]);
            yes.Instructions.Insert(0,phi);
        }
        if(shape=="unknown-address")guard.Instructions.RemoveAt(0);
        if(shape=="multiple-definition-address")guard.Instructions.Insert(0,new(17,OpCode.Move,address,new Immediate(0x10000)));
        foreach(var block in new[]{guard,plain,init,yes,no})block.CalculateBlockType();
        var before=graph.Blocks.Select(b=>(b.ID,string.Join(";",b.Instructions),string.Join(",",b.Predecessors.Select(p=>p.ID)),string.Join(",",b.Successors.Select(s=>s.ID)))).ToArray();
        Assert.That(MetadataInitForkRecovery.Run(graph),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(graph.Blocks.Contains(init),Is.False);
            Assert.That(guard.Successors,Is.EqualTo(new[]{plain}));
            Assert.That(yes.Predecessors,Is.EqualTo(new[]{plain}));
            Assert.That(no.Predecessors,Is.EqualTo(new[]{plain}));
            Assert.That(plain.Successors,Is.EqualTo(new[]{yes,no}));
            if(shape=="same-phi")Assert.That(yes.Instructions[0].Operands.Count,Is.EqualTo(2));
        }
        else Assert.That(graph.Blocks.Select(b=>(b.ID,string.Join(";",b.Instructions),string.Join(",",b.Predecessors.Select(p=>p.ID)),string.Join(",",b.Successors.Select(s=>s.ID)))).ToArray(),Is.EqualTo(before));
    }
}
