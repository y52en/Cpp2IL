using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ParameterizedBaseInitializerTests
{
    [TestCase(0,"valid",true)]
    [TestCase(1,"valid",true)]
    [TestCase(2,"valid",true)]
    [TestCase(1,"own-prefix",true)]
    [TestCase(1,"own-suffix",true)]
    [TestCase(1,"own-interleaved-before",true)]
    [TestCase(1,"own-interleaved-after",true)]
    [TestCase(1,"interleaved-overlap",false)]
    [TestCase(1,"interleaved-unknown",false)]
    [TestCase(1,"wrong-constant",false)]
    [TestCase(1,"wrong-width",false)]
    [TestCase(1,"wrong-field",false)]
    [TestCase(1,"wrong-offset",false)]
    [TestCase(1,"wrong-type",false)]
    [TestCase(1,"callback-inside",false)]
    [TestCase(1,"missing-store",false)]
    [TestCase(1,"duplicate-store",false)]
    [TestCase(1,"wrong-call",false)]
    [TestCase(1,"wrong-self",false)]
    [TestCase(1,"virtual-call",false)]
    [TestCase(1,"nullchecked-call",false)]
    [TestCase(1,"duplicate-call",false)]
    [TestCase(1,"ambiguous-template",false)]
    [TestCase(1,"unmatched-parent-prefix",false)]
    [TestCase(1,"unknown-memory-prefix",false)]
    [TestCase(1,"reassigned-this",false)]
    [TestCase(1,"late-argument",false)]
    public void ExactParameterizedParentSequencePreservesStoreAndBaseOrdering(int basePosition,string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var root=app.SystemTypes.SystemObjectType;
        var parent=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","Parent",root,TypeAttributes.Public);
        var child=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","Child",parent,TypeAttributes.Public);
        var state=parent.InjectFieldContext("NextState",app.SystemTypes.SystemInt32Type,FieldAttributes.Family);state.Offset=16;
        var owner=parent.InjectFieldContext("Owner",app.SystemTypes.SystemStringType,FieldAttributes.Family);owner.Offset=24;
        var own=child.InjectFieldContext("Own",app.SystemTypes.SystemInt32Type,FieldAttributes.Public);own.Offset=32;
        var ancestor=root.Methods.First(m=>m.Name==".ctor" && m.Parameters.Count==0);
        ancestor.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(true));
        var ctor=parent.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public,app.SystemTypes.SystemStringType);
        var parentThis=new LocalVariable("this",new(null,"this"),parent){IsThis=true};
        var parentArg=new LocalVariable("owner",new(null,"owner"),app.SystemTypes.SystemStringType);
        ctor.ParameterLocals=[parentThis,parentArg];ctor.Locals=[parentThis,parentArg];
        Instruction Store(FieldAnalysisContext field,LocalVariable receiver,IOperand value,int width)=>
            new(0,OpCode.Move,new FieldReference(field,receiver,field.Offset),value){NativeWriteSize=width};
        var native=new List<Instruction>{Store(state,parentThis,new Immediate(-1),4),Store(owner,parentThis,parentArg,8)};
        native.Insert(basePosition,new(1,OpCode.CallVoid,ancestor,parentThis));native.Add(new(2,OpCode.Return));
        ctor.ControlFlowGraph=new(native);
        var template=ParameterizedBaseInitializerRecovery.Extract(ctor);Assert.That(template,Is.Not.Null);
        Assert.That(template!.BasePosition,Is.EqualTo(basePosition));
        parent.PutExtraData(ParameterizedBaseInitializerRecovery.CacheKey,
            shape=="ambiguous-template"?new[]{template,template}:new[]{template});
        var caller=child.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public,app.SystemTypes.SystemStringType);
        var self=new LocalVariable("this",new(null,"this"),child){IsThis=true};
        var arg=new LocalVariable("owner",new(null,"owner"),app.SystemTypes.SystemStringType);
        caller.ParameterLocals=[self,arg];caller.Locals=[self,arg];
        var first=Store(state,self,new Immediate(-1),4);var last=Store(owner,self,arg,8);
        var call=new Instruction(1,OpCode.CallVoid,ancestor,self);
        var body=new List<Instruction>{first,last};body.Insert(basePosition,call);
        if(shape=="own-prefix")body.Insert(0,Store(own,self,new Immediate(3),4));
        if(shape=="own-suffix")body.Add(Store(own,self,new Immediate(3),4));
        if(shape=="own-interleaved-before")body.Insert(body.IndexOf(call),Store(own,self,new Immediate(3),4));
        if(shape=="own-interleaved-after")body.Insert(body.IndexOf(call)+1,Store(own,self,new Immediate(3),4));
        if(shape=="interleaved-overlap")
        {
            own.Offset=state.Offset;
            body.Insert(body.IndexOf(call),Store(own,self,new Immediate(3),4));
        }
        if(shape=="interleaved-unknown")body.Insert(body.IndexOf(call),Store(own,self,new LocalVariable("unknown",new(null,"unknown"),app.SystemTypes.SystemInt32Type),4));
        if(shape=="wrong-constant")first.SetOperand(1,new Immediate(2));
        if(shape=="wrong-width")last.NativeWriteSize=4;
        if(shape=="wrong-field")first.SetOperand(0,new FieldReference(own,self,own.Offset));
        if(shape=="wrong-offset")first.SetOperand(0,new FieldReference(state,self,20));
        if(shape=="wrong-type")last.SetOperand(1,new LocalVariable("different",new(null,"different"),app.SystemTypes.SystemInt32Type));
        if(shape=="callback-inside")body.Insert(1,new(4,OpCode.CallVoid,new StringLiteral("observable")));
        if(shape=="missing-store")body.Remove(last);
        if(shape=="duplicate-store")body.Insert(1,Store(state,self,new Immediate(-1),4));
        if(shape=="wrong-call")call.SetOperand(0,ctor);
        if(shape=="wrong-self")last.SetOperand(0,new FieldReference(owner,new("other",new(null,"other"),child),24));
        if(shape=="virtual-call")call.NativeVirtualDispatch=true;
        if(shape=="nullchecked-call")call.NativeNullCheckedCall=true;
        if(shape=="duplicate-call")body.Add(new(5,OpCode.CallVoid,ancestor,self));
        if(shape=="unmatched-parent-prefix")body.Insert(0,Store(state,self,new Immediate(7),4));
        if(shape=="unknown-memory-prefix")body.Insert(0,new(5,OpCode.Move,new MemoryOperand(self,addend:16),new Immediate(7)){NativeWriteSize=4});
        if(shape=="reassigned-this")body.Insert(0,new(5,OpCode.Move,self,new LocalVariable("other",new(null,"other"),child)));
        if(shape=="late-argument")
        {
            var late=new LocalVariable("late",new(null,"late"),app.SystemTypes.SystemStringType);
            last.SetOperand(1,late);body.Add(new(6,OpCode.Move,late,arg));
        }
        body.Add(new(7,OpCode.Return));caller.ControlFlowGraph=new(body);
        var before=caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(ParameterizedBaseInitializerRecovery.Recover(caller),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(call.Operands[0],Is.SameAs(ctor));Assert.That(call.Operands[1],Is.SameAs(self));
            Assert.That(call.Operands[2],Is.SameAs(arg));
            Assert.That(first.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(last.OpCode,Is.EqualTo(OpCode.Nop));
            Assert.That(state.Visibility,Is.EqualTo(FieldAttributes.Family));
        }
        else Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before),"never partially consume initializer writes");
    }
}
