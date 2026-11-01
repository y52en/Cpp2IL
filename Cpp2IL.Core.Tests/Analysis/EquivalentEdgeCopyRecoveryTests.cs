using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class EquivalentEdgeCopyRecoveryTests
{
    [TestCase("zero",true)]
    [TestCase("source",true)]
    [TestCase("different-value",false)]
    [TestCase("different-source",false)]
    [TestCase("different-destination",false)]
    [TestCase("different-width",false)]
    [TestCase("memory-read",false)]
    [TestCase("memory-write",false)]
    [TestCase("callback",false)]
    [TestCase("phi-successor",false)]
    [TestCase("missing-branch",false)]
    [TestCase("duplicate-edge",false)]
    [TestCase("clobber",false)]
    public void OnlyIdenticalCopiesShareABlockAndBothPathValuesArePreserved(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string name)=>new(name,new(null,name),t.SystemInt64Type);
        var input=Local("input");var other=Local("other");var result=Local("result");var alternate=Local("alternate");
        var graph=new ISILControlFlowGraph([]);
        var guardA=new Block{ID=20};var guardB=new Block{ID=21};var left=new Block{ID=22};var right=new Block{ID=23};var merge=new Block{ID=24};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,guardA,guardB,left,right,merge];
        foreach(var block in graph.Blocks){block.Predecessors.Clear();block.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guardA);Edge(guardA,left);Edge(guardA,guardB);Edge(guardB,right);Edge(left,merge);Edge(right,merge);Edge(merge,graph.ExitBlock);
        guardA.Instructions=[new(0,OpCode.ConditionalJump,left,input)];guardB.Instructions=[new(1,OpCode.Jump,right)];
        IOperand value=shape is "source" or "different-source"?input:new Immediate(0);
        var a=new Instruction(-1,OpCode.Move,result,value);
        var b=new Instruction(-1,OpCode.Move,shape=="different-destination"?alternate:result,
            shape=="different-value"?new Immediate(1):shape=="different-source"?other:value is Immediate?new Immediate(0):value);
        left.Instructions=[a,new(2,OpCode.Jump,merge)];right.Instructions=[b,new(3,OpCode.Jump,merge)];
        merge.Instructions=[new(4,OpCode.Return,result)];
        if(shape=="different-width")b.NativeRegisterCopySize=4;
        if(shape=="memory-read"){b.SetOperand(1,new MemoryOperand(input));b.NativeReadSize=8;}
        if(shape=="memory-write"){b.SetOperand(0,new MemoryOperand(input));b.NativeWriteSize=8;}
        if(shape=="callback")right.Instructions.Insert(0,new(5,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="phi-successor")merge.Instructions.Insert(0,new(5,OpCode.Phi,result,input,other));
        if(shape=="missing-branch")guardB.Instructions.Clear();
        if(shape=="duplicate-edge"){Edge(guardB,left);guardB.Instructions=[new(5,OpCode.ConditionalJump,left,input)];}
        if(shape=="clobber")b.ImplicitDefinition=new(null,"X0");
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemInt64Type,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=graph};
        var oldBlocks=graph.Blocks.ToArray();var oldInstructions=graph.Instructions.ToArray();
        var before=shape is "zero" or "source"?new[]{Trace(left,merge,input,result,7),Trace(right,merge,input,result,11)}:[];
        Assert.That(EquivalentEdgeCopyRecovery.Run(method),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(graph.Blocks.Contains(right),Is.False);
            Assert.That(guardB.Successors.Single(),Is.SameAs(left));
            Assert.That(guardB.Instructions.Single().Operands[0],Is.SameAs(left));
            Assert.That(left.Predecessors,Is.EquivalentTo(new[]{guardA,guardB}));
            Assert.That(merge.Predecessors,Is.EqualTo(new[]{left}));
            Assert.That(new[]{Trace(left,merge,input,result,7),Trace(left,merge,input,result,11)},Is.EqualTo(before));
            Assert.That(EquivalentEdgeCopyRecovery.Run(method),Is.Zero);
        }
        else
        {
            Assert.That(graph.Blocks,Is.EqualTo(oldBlocks));
            Assert.That(graph.Instructions,Is.EqualTo(oldInstructions));
            Assert.That(guardB.Successors.Contains(right),Is.True);
        }
    }
    static long Trace(Block block,Block merge,LocalVariable input,LocalVariable result,long value)
    {
        var locals=new Dictionary<LocalVariable,long>{{input,value}};
        foreach(var i in block.Instructions.Where(i=>i.OpCode==OpCode.Move))
            locals[(LocalVariable)i.Operands[0]]=i.Operands[1] is Immediate literal?literal.Value:locals[(LocalVariable)i.Operands[1]];
        return locals[(LocalVariable)merge.Instructions.Single().Operands[0]];
    }
}
