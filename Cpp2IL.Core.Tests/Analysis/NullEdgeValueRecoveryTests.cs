using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NullEdgeValueRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("zero-left",true)]
    [TestCase("not-equal",true)]
    [TestCase("not-condition",true)]
    [TestCase("local-source",true)]
    [TestCase("long-result",true)]
    [TestCase("source-redefined",false)]
    [TestCase("source-after-predicate",false)]
    [TestCase("source-address",false)]
    [TestCase("output-address",false)]
    [TestCase("value-source",false)]
    [TestCase("pointer-source",false)]
    [TestCase("runtime-handle-source",false)]
    [TestCase("unknown-source",false)]
    [TestCase("unknown-flag",false)]
    [TestCase("shared-flag",false)]
    [TestCase("guard-read",false)]
    [TestCase("nonnull-read",false)]
    [TestCase("self-copy-read",false)]
    [TestCase("return-old",false)]
    [TestCase("unknown-call",false)]
    [TestCase("indirect-jump",false)]
    [TestCase("cycle",false)]
    [TestCase("phi",false)]
    [TestCase("native-copy",false)]
    [TestCase("wide-copy",false)]
    [TestCase("reference-result",false)]
    [TestCase("unknown-comparison-width",false)]
    [TestCase("narrow-comparison",false)]
    [TestCase("integer-source-view",false)]
    public void NullValueOnlyReplacesASyntheticCopyDeadOnEveryNonNullPath(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string name,TypeAnalysisContext? type)=>new(name,new(null,name),type);
        var source=Local("source",t.SystemStringType);var other=Local("other",t.SystemStringType);
        var output=Local("output",shape=="long-result"?t.SystemInt64Type:shape=="reference-result"?t.SystemObjectType:t.SystemBooleanType);
        var flag=Local("flag",t.SystemBooleanType);var observed=Local("observed",t.SystemBooleanType);
        var graph=new ISILControlFlowGraph([]);var guard=new Block{ID=20};var nullPath=new Block{ID=21};
        var nonnull=new Block{ID=22};var merge=new Block{ID=23};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,guard,nullPath,nonnull,merge];
        foreach(var b in graph.Blocks){b.Predecessors.Clear();b.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,nullPath);Edge(guard,nonnull);Edge(nullPath,merge);Edge(nonnull,merge);Edge(merge,graph.ExitBlock);
        graph.EntryBlock.Instructions=[new(0,OpCode.Jump,guard)];
        var comparison=new Instruction(1,OpCode.CheckEqual,flag,source,new Immediate(0)){NativeComparisonSize=app.Binary.PointerSizeBytes};
        var copy=new Instruction(-1,OpCode.Move,output,source);
        var jump=new Instruction(2,OpCode.ConditionalJump,nullPath,flag);
        guard.Instructions=[comparison,copy,jump];
        nullPath.Instructions=[new(3,OpCode.Jump,merge)];
        nonnull.Instructions=[new(-1,OpCode.Move,output,new Immediate(1)),new(4,OpCode.Jump,merge)];
        merge.Instructions=[new(5,OpCode.Return,output)];
        var observer=new InjectedMethodAnalysisContext(t.SystemObjectType,"Observer",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",output.Type!,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=graph};
        method.ParameterLocals=[source,other];
        if(shape=="zero-left")comparison.SetOperands(flag,new Immediate(0),source);
        if(shape=="not-equal"){comparison.OpCode=OpCode.CheckNotEqual;jump.SetOperand(0,nonnull);}
        if(shape=="not-condition")
        {
            var inverse=Local("inverse",t.SystemBooleanType);guard.Instructions.Insert(2,new(6,OpCode.Not,inverse,flag));
            jump.SetOperands(nonnull,inverse);
        }
        if(shape=="local-source")
        {
            method.ParameterLocals=[other];graph.EntryBlock.Instructions.Insert(0,new(6,OpCode.Move,source,other));
        }
        if(shape=="source-redefined")nullPath.Instructions.Insert(0,new(6,OpCode.Move,source,other));
        if(shape=="source-after-predicate")
        {
            method.ParameterLocals=[other];guard.Instructions.Insert(1,new(6,OpCode.Move,source,other));
        }
        if(shape=="source-address")graph.EntryBlock.Instructions.Insert(0,new(6,OpCode.CallVoid,observer,new AddressOf(source)));
        if(shape=="output-address")graph.EntryBlock.Instructions.Insert(0,new(6,OpCode.CallVoid,observer,new AddressOf(output)));
        if(shape=="value-source")source.Type=t.SystemInt64Type;
        if(shape=="pointer-source")source.Type=new PointerTypeAnalysisContext(t.SystemInt64Type);
        if(shape=="runtime-handle-source")source.Type=new RuntimeMethodInfoAnalysisContext(observer,t.SystemObjectType.DeclaringAssembly);
        if(shape=="unknown-source")source.Type=null;
        if(shape=="unknown-flag")flag.Type=null;
        if(shape=="shared-flag")nonnull.Instructions.Insert(0,new(6,OpCode.Move,flag,new Immediate(0)));
        if(shape=="guard-read")guard.Instructions.Insert(guard.Instructions.Count-1,new(6,OpCode.Move,observed,output));
        if(shape=="nonnull-read")nonnull.Instructions.Insert(0,new(6,OpCode.CallVoid,observer,output));
        if(shape=="self-copy-read")nonnull.Instructions.Insert(0,new(6,OpCode.Move,output,output));
        if(shape=="return-old")nonnull.Instructions=[new(6,OpCode.Return,output)];
        if(shape=="unknown-call")nonnull.Instructions.Insert(0,new(6,OpCode.CallVoid,new Immediate(0x1234)));
        if(shape=="indirect-jump")nonnull.Instructions.Insert(0,new(6,OpCode.IndirectJump,new Immediate(0x1234)));
        if(shape=="cycle")
        {
            graph.RemoveEdge(nonnull,merge);Edge(nonnull,nonnull);nonnull.Instructions=[new(6,OpCode.Jump,nonnull)];
        }
        if(shape=="phi")nonnull.Instructions.Insert(0,new(6,OpCode.Phi,observed,flag));
        if(shape=="native-copy")copy.Index=7;
        if(shape=="wide-copy")copy.NativeRegisterCopySize=8;
        if(shape=="unknown-comparison-width")comparison.NativeComparisonSize=0;
        if(shape=="narrow-comparison")comparison.NativeComparisonSize=4;
        if(shape=="integer-source-view")comparison.NativeIntegerSourceView=true;
        var original=graph.Instructions.Select(i=>i.ToString()).ToArray();
        var before=expected?new[]{Trace(graph,source,other,0),Trace(graph,source,other,123)}:[];
        Assert.That(NullEdgeValueRecovery.Run(method),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(copy.Operands[1],Is.TypeOf<Immediate>());
            Assert.That(((Immediate)copy.Operands[1]).Value,Is.Zero);
            Assert.That(new[]{Trace(graph,source,other,0),Trace(graph,source,other,123)},Is.EqualTo(before));
            Assert.That(before,Is.EqualTo(new long[]{0,1}));
            Assert.That(NullEdgeValueRecovery.Run(method),Is.Zero);
        }
        else Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(original));
    }
    static long Trace(ISILControlFlowGraph graph,LocalVariable source,LocalVariable other,long input)
    {
        var values=new Dictionary<LocalVariable,long>{{source,input},{other,input}};var block=graph.EntryBlock;
        long Value(IOperand operand)=>operand is Immediate literal?literal.Value:values[(LocalVariable)operand];
        for(var count=0;count<32;count++)
        {
            Block? next=null;
            foreach(var i in block.Instructions)
            {
                if(i.OpCode==OpCode.Move)values[(LocalVariable)i.Operands[0]]=Value(i.Operands[1]);
                else if(i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual)
                    values[(LocalVariable)i.Operands[0]]=(Value(i.Operands[1])==Value(i.Operands[2]))==(i.OpCode==OpCode.CheckEqual)?1:0;
                else if(i.OpCode==OpCode.Not)values[(LocalVariable)i.Operands[0]]=Value(i.Operands[1])==0?1:0;
                else if(i.OpCode==OpCode.Return)return Value(i.Operands[0]);
                else if(i.OpCode==OpCode.Jump)next=(Block)i.Operands[0];
                else if(i.OpCode==OpCode.ConditionalJump)next=Value(i.Operands[1])!=0?(Block)i.Operands[0]
                    :block.Successors.Single(b=>!ReferenceEquals(b,i.Operands[0]));
            }
            block=next??block.Successors.Single();
        }
        throw new System.InvalidOperationException("fixture did not return");
    }
}
