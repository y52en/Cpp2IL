using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ZeroStateConstructorRecoveryTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("exact",true)]
    [TestCase("alias",true)]
    [TestCase("nonzero-constant",false)]
    [TestCase("negative-zero",false)]
    [TestCase("unknown-store-width",false)]
    [TestCase("overlapping-stores",false)]
    [TestCase("header-store",false)]
    [TestCase("missing-object-proof",false)]
    [TestCase("class-initializer",false)]
    [TestCase("finalizer",false)]
    [TestCase("explicit-layout",false)]
    [TestCase("extra-constructor",false)]
    [TestCase("foreign-owner",false)]
    [TestCase("effect-before-base",false)]
    [TestCase("virtual-base",false)]
    [TestCase("wrong-receiver",false)]
    [TestCase("receiver-redefined",false)]
    [TestCase("missing-template",false)]
    [TestCase("invalid-parameter-index",false)]
    [TestCase("reference-parameter",false)]
    [TestCase("linear-call-barrier",true)]
    [TestCase("linear-alias",true)]
    [TestCase("merged-call-block",false)]
    [TestCase("branched-allocation-block",false)]
    [TestCase("effect-on-continuation",false)]
    public void OnlyTheProvenZeroStateIdentityCanReplaceObjectBaseCall(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","ZeroState",
            types.SystemObjectType,TypeAttributes.Public|(shape=="explicit-layout"?TypeAttributes.ExplicitLayout:0));
        var ctor=owner.InjectMethodContext(".ctor",types.SystemVoidType,MethodAttributes.Public,
            shape=="reference-parameter"?types.SystemObjectType:types.SystemInt32Type,types.SystemSingleType);
        var a=owner.InjectFieldContext("a",types.SystemInt32Type,FieldAttributes.Public);a.Offset=16;
        var b=owner.InjectFieldContext("b",types.SystemSingleType,FieldAttributes.Public);b.Offset=20;
        var parent=types.SystemObjectType.Methods.Single(m=>m.Name==".ctor"&&m.Parameters.Count==0);
        if(shape!="missing-object-proof")parent.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,
            new TrivialConstructorRecovery.ObjectProof(true));
        var assignments=new[]{
            new InlinedConstructorRecovery.Assignment(a,shape=="invalid-parameter-index"?9:0,
                shape=="nonzero-constant"?new Immediate(1):null){NativeWidth=shape=="unknown-store-width"?0:4},
            new InlinedConstructorRecovery.Assignment(b,1,
                shape=="negative-zero"?new FloatLiteral(-0f):null){NativeWidth=4}};
        var template=new InlinedConstructorRecovery.Template(ctor,assignments,parent);
        if(shape=="foreign-owner")template=template with {Constructor=parent};
        if(shape=="overlapping-stores")b.Offset=16;
        if(shape=="header-store")a.Offset=8;
        if(shape=="class-initializer")owner.InjectMethodContext(".cctor",types.SystemVoidType,MethodAttributes.Static);
        if(shape=="finalizer")owner.InjectMethodContext("Finalize",types.SystemVoidType,MethodAttributes.Family);
        owner.PutExtraData(InlinedConstructorRecovery.CacheKey,shape=="missing-template"?[]:
            shape=="extra-constructor"?new[]{template,template}:new[]{template});
        var method=owner.InjectMethodContext("Caller",types.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var obj=Local("allocated",owner);var alias=Local("alias",owner);
        var allocation=new Instruction(0,OpCode.Newobj,obj,owner);
        var call=new Instruction(2,OpCode.CallVoid,parent,shape=="wrong-receiver"?Local("other",owner):shape=="alias"?alias:obj)
            {NativeVirtualDispatch=shape=="virtual-base"};
        var store=new Instruction(3,OpCode.Move,new FieldReference(a,obj,16),new Immediate(38)){NativeWriteSize=4};
        var branch=new Instruction(4,OpCode.CheckEqual,Local("condition",types.SystemBooleanType),new Immediate(1),new Immediate(0));
        var list=new List<Instruction>{allocation};
        if(shape=="alias")list.Add(new(1,OpCode.Move,alias,obj));
        if(shape=="effect-before-base")list.Add(new(1,OpCode.CallVoid,new StringLiteral("callback")));
        list.AddRange([call,store,branch,new(5,OpCode.Return)]);
        if(shape=="receiver-redefined")list.Insert(3,new(6,OpCode.Move,obj,alias));
        method.ControlFlowGraph=new(list);
        if(shape is "linear-call-barrier" or "linear-alias" or "merged-call-block"
            or "branched-allocation-block" or "effect-on-continuation")
        {
            var graph=new ISILControlFlowGraph([]);
            var first=new Block{ID=2};var next=new Block{ID=3};var other=new Block{ID=4};
            graph.Blocks.AddRange([first,next,other]);
            graph.EntryBlock.Successors.Add(first);first.Predecessors.Add(graph.EntryBlock);
            first.Instructions.Add(allocation);first.Successors.Add(next);next.Predecessors.Add(first);
            if(shape=="linear-alias")next.Instructions.Add(new(1,OpCode.Move,alias,obj));
            if(shape=="linear-alias")call.SetOperands([parent,alias]);
            if(shape=="effect-on-continuation")next.Instructions.Add(new(1,OpCode.CallVoid,new StringLiteral("callback")));
            next.Instructions.AddRange([call,store,branch,new(5,OpCode.Return)]);
            next.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(next);
            if(shape=="merged-call-block")
            {graph.EntryBlock.Successors.Add(other);other.Predecessors.Add(graph.EntryBlock);other.Successors.Add(next);next.Predecessors.Add(other);}
            if(shape=="branched-allocation-block")
            {first.Successors.Add(other);other.Predecessors.Add(first);other.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(other);}
            method.ControlFlowGraph=graph;
            list=graph.Instructions.ToList();
        }
        var original=list.ToDictionary(i=>i,i=>(i.OpCode,Operands:i.Operands.ToArray()));
        Assert.That(ZeroStateConstructorRecovery.Recover(method),Is.EqualTo(expected?1:0));
        Assert.That(call.Operands[0],Is.SameAs(expected?ctor:parent));
        foreach(var instruction in list.Where(i=>!expected||!ReferenceEquals(i,call)))
        {
            Assert.That(instruction.OpCode,Is.EqualTo(original[instruction].OpCode));
            Assert.That(instruction.Operands,Is.EqualTo(original[instruction].Operands));
        }
        if(expected)
        {
            Assert.That(call.Operands.Count,Is.EqualTo(4));
            Assert.That(call.Operands[2],Is.EqualTo(new Immediate(0)));
            Assert.That(call.Operands[3],Is.EqualTo(new FloatLiteral(0f)));
            Assert.That(store.OpCode,Is.EqualTo(OpCode.Move),"Original field initialization must remain intact");
        }
    }
}
