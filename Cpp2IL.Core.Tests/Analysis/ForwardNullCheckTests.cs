using System;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardNullCheckTests
{
    [TestCase("load",true)]
    [TestCase("store",true)]
    [TestCase("copied-receiver",true)]
    [TestCase("direct-call",true)]
    [TestCase("direct-void",true)]
    [TestCase("different-field",false)]
    [TestCase("static-field",false)]
    [TestCase("nested-field",false)]
    [TestCase("raw-memory",false)]
    [TestCase("field-rhs",false)]
    [TestCase("live-result",false)]
    [TestCase("overwrite",false)]
    [TestCase("effect",false)]
    [TestCase("branch",false)]
    [TestCase("virtual-base-call",false)]
    [TestCase("constructor",false)]
    [TestCase("static-call",false)]
    [TestCase("different-call",false)]
    [TestCase("unmaterialized-argument",false)]
    public void ManagedDereferencePreservesFirstExceptionAndNeverInventsVirtualDispatch(string shape,bool expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Owner",t.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("value",t.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
        if(shape=="static-field")field.Attributes|=FieldAttributes.Static;
        var input=new LocalVariable("input",new(null,"input"),owner);
        var alias=new LocalVariable("alias",new(null,"alias"),owner);
        var other=new LocalVariable("other",new(null,"other"),owner);
        var result=new LocalVariable("result",new(null,"result"));
        var loaded=new LocalVariable("loaded",new(null,"loaded"),t.SystemInt32Type);
        var guard=new Instruction(0,OpCode.Call,new Immediate(0xa61e60),result,input);
        var list=new List<Instruction>{guard};
        if(shape=="copied-receiver")list.Add(new(1,OpCode.Move,alias,input));
        if(shape=="live-result")list.Add(new(1,OpCode.Move,other,result));
        if(shape=="overwrite")list.Add(new(1,OpCode.Move,input,other));
        if(shape=="effect")list.Add(new(1,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape=="branch")list.Add(new(1,OpCode.ConditionalJump,new Instruction(99,OpCode.Return),other));
        var reference=new FieldReference(field,shape=="different-field"?other:shape=="copied-receiver"?alias:input,16);
        if(shape=="nested-field")reference.Parent=new FieldReference(field,other,16);
        Instruction operation;
        var direct=shape.Contains("call") || shape is "constructor" or "direct-void" or "unmaterialized-argument";
        if(direct)
        {
            var target=new InjectedMethodAnalysisContext(owner,shape=="constructor"?".ctor":"Read",t.SystemVoidType,
                MethodAttributes.Public|(shape=="virtual-base-call"?MethodAttributes.Virtual:0)
                |(shape=="static-call"?MethodAttributes.Static:0),shape=="unmaterialized-argument"?[t.SystemInt32Type]:[]);
            operation=shape=="direct-call"?new(2,OpCode.Call,target,loaded,input):new(2,OpCode.CallVoid,target,shape=="different-call"?other:input);
            if(shape=="unmaterialized-argument")operation.AddOperands([reference]);
        }
        else operation=shape is "store" or "field-rhs"?new(2,OpCode.Move,reference,shape=="field-rhs"?new FieldReference(field,other,16):new Immediate(0))
            :new(2,OpCode.Move,loaded,shape=="raw-memory"?new MemoryOperand(input):reference);
        list.Add(operation);list.Add(new(3,OpCode.Return));var cfg=new ISILControlFlowGraph(list);
        Assert.That(ForwardNullCheckRecovery.TryPreserveAtManagedDereference(cfg,guard),Is.EqualTo(expected));
        Assert.That(guard.OpCode,Is.EqualTo(OpCode.Call));
        Assert.That(operation.NativeVirtualDispatch,Is.False);
        Assert.That(operation.NativeNullCheckedCall,Is.EqualTo(expected && direct));
    }

    [TestCase("dead-copy", true)]
    [TestCase("live-copy", false)]
    [TestCase("observable-call", false)]
    public void RevisitAfterDeadCodeCleanupStillRequiresTheOriginalSafetyProof(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var input = new LocalVariable("input", new Register(null, "input"), t.SystemStringType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var temporary = new LocalVariable("temporary", new Register(null, "temporary"));
        var target = new InjectedMethodAnalysisContext(t.SystemObjectType, "Read", t.SystemVoidType, MethodAttributes.Public, []);
        var guard = new Instruction(0, OpCode.Call, new Immediate(0xa61e60), result, input);
        var virtualCall = new Instruction(3, OpCode.CallVoid, target, input) { NativeVirtualDispatch = true };
        var instructions = new List<Instruction> {guard, new(1, OpCode.Move, temporary, result)};
        if (shape == "observable-call") instructions.Add(new(2, OpCode.CallVoid, new Immediate(123), input));
        instructions.Add(virtualCall);
        if (shape == "live-copy") instructions.Add(new(4, OpCode.CallVoid, new Immediate(456), temporary));
        instructions.Add(new(5, OpCode.Return));
        var graph = new ISILControlFlowGraph(instructions);
        Assert.That(ForwardNullCheckRecovery.FollowedBySameVirtualReceiver(graph, guard), Is.False);
        DeadCodeEliminator.Run(graph);
        Assert.That(ForwardNullCheckRecovery.FollowedBySameVirtualReceiver(graph, guard), Is.EqualTo(expected));
        Assert.That(guard.OpCode, Is.EqualTo(OpCode.Call), "proof queries must not remove native calls");
    }

    [Test]
    public void FullNullHelperFingerprintIsRequired()
    {
        var bytes = Convert.FromHexString("400000b4c0035fd6e00301aadd2d0114");
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes), Is.True);
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes[..^4]), Is.False);
        bytes[^1] ^= 1;
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes), Is.False);
    }

    [TestCase("same", true)]
    [TestCase("copy", true)]
    [TestCase("linear-block", true)]
    [TestCase("different", false)]
    [TestCase("nonvirtual", false)]
    [TestCase("value-receiver", false)]
    [TestCase("overwrite", false)]
    [TestCase("call", false)]
    [TestCase("load", false)]
    [TestCase("store", false)]
    [TestCase("live-result", false)]
    [TestCase("branch", false)]
    public void NullThrowMustBePreservedByNextObservableCallOnSameValue(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var input = new LocalVariable("input", new Register(null, "input"), shape == "value-receiver" ? t.SystemInt32Type : t.SystemStringType);
        var alias = new LocalVariable("alias", new Register(null, "alias"), t.SystemStringType);
        var other = new LocalVariable("other", new Register(null, "other"), t.SystemStringType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var target = new InjectedMethodAnalysisContext(t.SystemObjectType, "Read", t.SystemVoidType, MethodAttributes.Public, []);
        var guard = new Instruction(0, OpCode.Call, new Immediate(0xa61e60), result, input);
        var call = new Instruction(10, OpCode.CallVoid, target, shape == "different" ? other : shape == "copy" ? alias : input)
            { NativeVirtualDispatch = shape != "nonvirtual" };
        var instructions = new List<Instruction> { guard };
        if (shape == "copy") instructions.Add(new(1, OpCode.Move, alias, input));
        if (shape == "overwrite") instructions.Add(new(1, OpCode.Move, input, other));
        if (shape == "call") instructions.Add(new(1, OpCode.CallVoid, new Immediate(123), input));
        if (shape == "load") instructions.Add(new(1, OpCode.Move, other, new MemoryOperand(input)));
        if (shape == "store") instructions.Add(new(1, OpCode.Move, new MemoryOperand(other), input));
        if (shape == "live-result") instructions.Add(new(1, OpCode.Move, other, result));
        if (shape == "branch") instructions.Add(new(1, OpCode.ConditionalJump, call, other));
        if (shape == "linear-block") instructions.Add(new(1, OpCode.Jump, call));
        instructions.Add(call); instructions.Add(new(11, OpCode.Return));
        var cfg = new ISILControlFlowGraph(instructions);
        Assert.That(ForwardNullCheckRecovery.FollowedBySameVirtualReceiver(cfg, guard), Is.EqualTo(expected));
        Assert.That(guard.OpCode, Is.EqualTo(OpCode.Call), "proof query must not mutate the graph");
    }
}
