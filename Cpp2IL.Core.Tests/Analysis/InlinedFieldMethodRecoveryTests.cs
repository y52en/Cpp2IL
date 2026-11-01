using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlinedFieldMethodRecoveryTests
{
    [TestCase("valid")]
    [TestCase("value")]
    [TestCase("receiver")]
    [TestCase("callee")]
    [TestCase("dispatch")]
    [TestCase("effect")]
    [TestCase("ambiguous")]
    [TestCase("call-unused-result")]
    [TestCase("call-used-result")]
    [TestCase("call-result-is-receiver")]
    [TestCase("call-nested-result")]
    public void ConstantPublicWrapperPreservesItsExactInheritedVirtualTail(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Parent",t.SystemObjectType,TypeAttributes.Public);
        var owner=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","Window",parent,TypeAttributes.Public);
        var close=parent.InjectMethodContext("Close",t.SystemVoidType,MethodAttributes.Public | MethodAttributes.Virtual);
        var other=parent.InjectMethodContext("Other",t.SystemVoidType,MethodAttributes.Public | MethodAttributes.Virtual);
        var wrapper=owner.InjectMethodContext("Cancel",t.SystemVoidType,MethodAttributes.Public);
        var field=owner.InjectFieldContext("selection",t.SystemInt32Type,FieldAttributes.Private);field.Offset=16;
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};wrapper.ParameterLocals=[self];
        wrapper.ControlFlowGraph=new([new(0,OpCode.Move,new FieldReference(field,self,16),new Immediate(0)),
            new(1,OpCode.CallVoid,close,self){NativeVirtualDispatch=true},new(2,OpCode.Return)]);
        var template=InlinedFieldMethodRecovery.Extract(wrapper);
        Assert.That(template,Is.Not.Null);
        Assert.That(template!.TailVirtualDispatch,Is.True);
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey,shape=="ambiguous" ? new[]{template,template} : new[]{template});
        var caller=owner.InjectMethodContext("Caller",t.SystemVoidType,MethodAttributes.Public);
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),owner);
        var otherReceiver=new LocalVariable("other",new Register(null,"other"),owner);
        var store=new Instruction(0,OpCode.Move,new FieldReference(field,receiver,16),new Immediate(shape=="value" ? 1 : 0));
        var tail=new Instruction(1,OpCode.CallVoid,shape=="callee" ? other : close,shape=="receiver" ? otherReceiver : receiver)
            {NativeVirtualDispatch=shape!="dispatch"};
        var result=new LocalVariable("result",new Register(null,"result"),t.SystemObjectType);
        if(shape.StartsWith("call-"))
        {
            tail.OpCode=OpCode.Call;
            tail.SetOperands(close,shape=="call-result-is-receiver" ? receiver : result,receiver);
        }
        caller.ControlFlowGraph=shape=="effect" ? new([store,new(3,OpCode.CallVoid,new StringLiteral("business")),tail,new(2,OpCode.Return)])
            : new([store,tail,new(2,OpCode.Return)]);
        if(shape=="call-used-result")caller.ControlFlowGraph.Blocks.First(b=>b.Instructions.Contains(tail))
            .Instructions.Insert(2,new(4,OpCode.CallVoid,new StringLiteral("consume"),result));
        if(shape=="call-nested-result")caller.ControlFlowGraph.Blocks.First(b=>b.Instructions.Contains(tail))
            .Instructions.Insert(2,new(4,OpCode.Move,new LocalVariable("loaded",new Register(null,"loaded")),new MemoryOperand(new MemoryOperand(result))));
        var valid=shape is "valid" or "call-unused-result";
        Assert.That(InlinedFieldMethodRecovery.Run(caller),Is.EqualTo(valid ? 1 : 0));
        if(valid)
        {
            Assert.That(store.Operands,Is.EqualTo(new IOperand[]{wrapper,receiver}));
            Assert.That(store.NativeVirtualDispatch,Is.False);
            Assert.That(tail.OpCode,Is.EqualTo(OpCode.Nop));
        }
    }

    [TestCase("bool",2)]
    [TestCase("reference",1)]
    [TestCase("float",0)]
    [TestCase("byte",256)]
    public void ConstantTemplateNeverGuessesAValueOfAnotherManagedKind(string kind,long value)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","InvalidConstant",t.SystemObjectType,TypeAttributes.Public);
        var method=owner.InjectMethodContext("Reset",t.SystemVoidType,MethodAttributes.Public);
        var type=kind switch{"bool"=>t.SystemBooleanType,"reference"=>t.SystemObjectType,"float"=>t.SystemSingleType,_=>t.SystemByteType};
        var field=owner.InjectFieldContext("field",type,FieldAttributes.Private);field.Offset=16;
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};method.ParameterLocals=[self];
        method.ControlFlowGraph=new([new(0,OpCode.Move,new FieldReference(field,self,16),new Immediate(value)),new(1,OpCode.Return)]);
        Assert.That(InlinedFieldMethodRecovery.Extract(method),Is.Null);
    }

    [TestCase("private")]
    [TestCase("virtual")]
    [TestCase("missing-return")]
    [TestCase("unknown-store")]
    [TestCase("duplicate-store")]
    [TestCase("different-offset")]
    [TestCase("different-receiver")]
    [TestCase("extra-effect")]
    [TestCase("branch")]
    public void IncompleteOrDifferentNativeTemplateIsRejected(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var owner = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "NativeTemplate", types.SystemObjectType, TypeAttributes.Public);
        var method = owner.InjectMethodContext("Set", types.SystemVoidType, MethodAttributes.Public, types.SystemInt32Type);
        if (shape == "private") method.Attributes = MethodAttributes.Private;
        if (shape == "virtual") method.Attributes |= MethodAttributes.Virtual;
        var field = owner.InjectFieldContext("index", types.SystemInt32Type, FieldAttributes.Private); field.Offset = 16;
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var other = new LocalVariable("other", new Register(null, "other"), owner);
        var value = new LocalVariable("value", new Register(null, "value"), types.SystemInt32Type);
        method.ParameterLocals = [self, value];
        var store = new Instruction(0, OpCode.Move,
            new FieldReference(field, shape == "different-receiver" ? other : self, shape == "different-offset" ? 20 : 16), value);
        var instructions = new System.Collections.Generic.List<Instruction> { store };
        if (shape == "unknown-store") store.SetOperand(0, new MemoryOperand(self, addend: 16));
        if (shape == "duplicate-store") instructions.Add(new(1, OpCode.Move, new FieldReference(field, self, 16), value));
        if (shape == "extra-effect") instructions.Add(new(1, OpCode.CallVoid, new StringLiteral("unknown helper")));
        var returned = new Instruction(3, OpCode.Return);
        if (shape == "branch") instructions.Add(new(2, OpCode.ConditionalJump, returned, value));
        if (shape != "missing-return") instructions.Add(returned);
        method.ControlFlowGraph = new(instructions);
        Assert.That(InlinedFieldMethodRecovery.Extract(method), Is.Null);
    }

    [TestCase("valid")]
    [TestCase("different-value")]
    [TestCase("different-receiver")]
    [TestCase("different-offset")]
    [TestCase("different-callee")]
    [TestCase("virtual-call")]
    [TestCase("ambiguous")]
    [TestCase("intervening-effect")]
    [TestCase("self")]
    [TestCase("constructor")]
    public void CompleteTemplateAndCallerMustAgree(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var owner = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "Panel", types.SystemObjectType, TypeAttributes.Public);
        var method = owner.InjectMethodContext("SetData", types.SystemVoidType, MethodAttributes.Public, types.SystemInt32Type);
        var tail = owner.InjectMethodContext("Update", types.SystemVoidType, MethodAttributes.Public, types.SystemInt32Type);
        var field = owner.InjectFieldContext("index", types.SystemInt32Type, FieldAttributes.Private); field.Offset = 16;
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var parameter = new LocalVariable("index", new Register(null, "index"), types.SystemInt32Type);
        method.ParameterLocals = [self, parameter];
        method.ControlFlowGraph = new([new(0, OpCode.Move, new FieldReference(field, self, 16), parameter),
            new(1, OpCode.CallVoid, tail, self, parameter), new(2, OpCode.Return)]);
        var template = InlinedFieldMethodRecovery.Extract(method);
        Assert.That(template, Is.Not.Null);
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey,
            shape == "ambiguous" ? new[] { template!, template! } : new[] { template! });
        var caller = shape == "self" ? method : owner.InjectMethodContext(shape == "constructor" ? ".ctor" : "Caller", types.SystemVoidType, MethodAttributes.Public);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var other = new LocalVariable("other", new Register(null, "other"), owner);
        var value = new Immediate(7);
        var store = new Instruction(0, OpCode.Move, new FieldReference(field, receiver, shape == "different-offset" ? 20 : 16), value);
        var call = new Instruction(1, OpCode.CallVoid, shape == "different-callee" ? method : tail,
            shape == "different-receiver" ? other : receiver, shape == "different-value" ? new Immediate(8) : value)
            { NativeVirtualDispatch = shape == "virtual-call" };
        caller.ControlFlowGraph = shape == "intervening-effect"
            ? new([store, new(3, OpCode.CallVoid, tail, other, value), call, new(2, OpCode.Return)])
            : new([store, call, new(2, OpCode.Return)]);
        Assert.That(InlinedFieldMethodRecovery.Run(caller), Is.EqualTo(shape == "valid" ? 1 : 0));
        Assert.That(store.OpCode, Is.EqualTo(shape == "valid" ? OpCode.CallVoid : OpCode.Move));
        if (shape == "valid")
        {
            Assert.That(store.Operands[0], Is.SameAs(method));
            Assert.That(store.Operands[1], Is.SameAs(receiver));
            Assert.That(store.Operands[2], Is.EqualTo(value));
            Assert.That(call.OpCode, Is.EqualTo(OpCode.Nop));
        }
    }
}
