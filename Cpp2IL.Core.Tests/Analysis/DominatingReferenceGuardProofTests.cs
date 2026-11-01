using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DominatingReferenceGuardProofTests
{
    [TestCase("equal",true)]
    [TestCase("not-equal",true)]
    [TestCase("inverted",true)]
    [TestCase("swapped",true)]
    [TestCase("double-invert",true)]
    [TestCase("null-side-effect",true)]
    [TestCase("nonnull-side-effect",true)]
    [TestCase("wrong-polarity",false)]
    [TestCase("wrong-source",false)]
    [TestCase("same-name-impostor",false)]
    [TestCase("unknown-flag",false)]
    [TestCase("wrong-flag-type",false)]
    [TestCase("second-source-write",false)]
    [TestCase("source-defined-after-test",false)]
    [TestCase("bypass",false)]
    [TestCase("unknown-source",false)]
    [TestCase("value-source",false)]
    [TestCase("pointer-source",false)]
    [TestCase("guard-is-consumer",false)]
    public void ExistingNonNullEdgeMustDominateWithoutChangingAnyOriginalPath(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string n,TypeAnalysisContext? type=null)=>new(n,new Register(null,n),type);
        var source=Local("source",t.SystemObjectType);var other=Local("other",t.SystemObjectType);
        var flag=Local("flag",t.SystemBooleanType);var not=Local("not",t.SystemBooleanType);
        var twice=Local("twice",t.SystemBooleanType);
        var graph=new ISILControlFlowGraph([]);
        var guard=new Block{ID=10};var nonnull=new Block{ID=11};var nullPath=new Block{ID=12};var consumer=new Block{ID=13};
        graph.Blocks=[graph.EntryBlock,guard,nonnull,nullPath,consumer,graph.ExitBlock];
        foreach(var block in graph.Blocks){block.Successors.Clear();block.Predecessors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,nullPath);Edge(guard,nonnull);Edge(nonnull,consumer);
        Edge(nullPath,graph.ExitBlock);Edge(consumer,graph.ExitBlock);
        var equality=new Instruction(1,shape=="not-equal"?OpCode.CheckNotEqual:OpCode.CheckEqual,flag,source,new Immediate(0));
        var jump=new Instruction(4,OpCode.ConditionalJump,shape=="not-equal"?nonnull:nullPath,flag);
        guard.Instructions=[equality,jump];nonnull.Instructions=[new(5,OpCode.Jump,consumer)];
        nullPath.Instructions=[new(6,OpCode.Return)];consumer.Instructions=[new(7,OpCode.Return)];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Probe",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=graph,ParameterLocals=[source,other]};
        if(shape=="inverted"||shape=="double-invert") {
            guard.Instructions.Insert(1,new(2,OpCode.Not,not,flag));jump.SetOperands(nonnull,not);
            if(shape=="double-invert"){guard.Instructions.Insert(2,new(3,OpCode.Not,twice,not));jump.SetOperands(nullPath,twice);}
        }
        if(shape=="swapped")equality.SetOperands(flag,new Immediate(0),source);
        if(shape=="wrong-polarity")jump.SetOperand(0,nonnull);
        if(shape=="wrong-source")equality.SetOperand(1,other);
        if(shape=="same-name-impostor")equality.SetOperand(1,Local("source",t.SystemObjectType));
        if(shape=="unknown-flag")jump.SetOperand(1,Local("missing",t.SystemBooleanType));
        if(shape=="wrong-flag-type")flag.Type=t.SystemInt32Type;
        if(shape=="second-source-write")nonnull.Instructions.Insert(0,new(8,OpCode.Move,source,other));
        if(shape=="source-defined-after-test") {
            method.ParameterLocals=[other];guard.Instructions.Insert(1,new(8,OpCode.Move,source,other));
        }
        if(shape=="bypass")Edge(nullPath,consumer);
        if(shape=="unknown-source")source.Type=null;
        if(shape=="value-source")source.Type=t.SystemInt32Type;
        if(shape=="pointer-source")source.Type=new PointerTypeAnalysisContext(t.SystemObjectType);
        if(shape=="null-side-effect")nullPath.Instructions.Insert(0,new(9,OpCode.CallVoid,new Immediate(1234)));
        if(shape=="nonnull-side-effect")nonnull.Instructions.Insert(0,new(9,OpCode.CallVoid,new Immediate(1234)));
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(DominatingReferenceGuardProof.NonNullAt(method,source,shape=="guard-is-consumer"?guard:consumer),Is.EqualTo(expected));
        Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
    }
}
