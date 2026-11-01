using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InheritedFieldConstructorRecoveryTests
{
    [TestCase("field",true)]
    [TestCase("raw",true)]
    [TestCase("unproved-object",false)]
    [TestCase("unrelated-base",false)]
    [TestCase("unrelated-field",false)]
    [TestCase("template-partial",false)]
    [TestCase("template-unknown-width",false)]
    [TestCase("template-base-after-store",false)]
    [TestCase("call-partial",false)]
    [TestCase("field-partial",false)]
    [TestCase("call-unknown-width",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("other-receiver",false)]
    [TestCase("effect",false)]
    [TestCase("call-base-after-store",false)]
    public void ExactCompleteChildBodyMayMatchInheritedStoreWithoutInventingParentEffects(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","ParentFields",types.SystemObjectType,TypeAttributes.Public);
        var child=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","ChildFields",parent,TypeAttributes.Public);
        var other=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","UnrelatedFields",types.SystemObjectType,TypeAttributes.Public);
        var field=(shape=="unrelated-field"?other:parent).InjectFieldContext("Name",types.SystemStringType,FieldAttributes.Public);field.Offset=24;
        MethodAnalysisContext baseCtor=new InjectedMethodAnalysisContext(types.SystemObjectType,".ctor",types.SystemVoidType,MethodAttributes.Public,[]);
        baseCtor.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(shape!="unproved-object"));
        if(shape=="unrelated-base")baseCtor=other.InjectMethodContext(".ctor",types.SystemVoidType,MethodAttributes.Public,[]);
        var ctor=child.InjectMethodContext(".ctor",types.SystemVoidType,MethodAttributes.Public,[types.SystemStringType]);
        var self=new LocalVariable("this",new Register(null,"this"),child){IsThis=true};
        var parameter=new LocalVariable("name",new Register(null,"parameter"),types.SystemStringType);
        ctor.ParameterLocals=[self,parameter];
        var baseCall=new Instruction(0,OpCode.CallVoid,baseCtor,self);
        var templateStore=new Instruction(1,OpCode.Move,new FieldReference(field,self,24),parameter)
            {NativeWriteSize=shape=="template-partial"?4:shape=="template-unknown-width"?0:8};
        ctor.ControlFlowGraph=new(shape=="template-base-after-store"
            ?[templateStore,baseCall,new(2,OpCode.Return)]:[baseCall,templateStore,new(2,OpCode.Return)]);
        var template=InlinedConstructorRecovery.Extract(ctor);
        if(shape.StartsWith("template-") || shape is "unproved-object" or "unrelated-base" or "unrelated-field")
        {Assert.That(template,Is.Null);return;}
        Assert.That(template,Is.Not.Null);
        var caller=new InjectedMethodAnalysisContext(child,"Create",child,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=new LocalVariable("obj",new Register(null,"obj"),child);
        var different=new LocalVariable("other",new Register(null,"other"),child);
        var argument=new LocalVariable("argument",new Register(null,"argument"),types.SystemStringType);
        caller.ParameterLocals=[argument];
        var allocation=new Instruction(3,OpCode.Newobj,obj,child);
        var call=new Instruction(4,OpCode.CallVoid,baseCtor,obj);
        IOperand target=shape is "field" or "field-partial" ?new FieldReference(field,obj,24)
            :new MemoryOperand(shape=="other-receiver"?different:obj,addend:shape=="wrong-offset"?25:24);
        var store=new Instruction(5,OpCode.Move,target,argument)
            {NativeWriteSize=shape is "call-partial" or "field-partial"?4:shape=="call-unknown-width"?0:8};
        var body=new List<Instruction>{allocation,call,store,new(6,OpCode.Return,obj)};
        if(shape=="effect")body.Insert(2,new(8,OpCode.CallVoid,new StringLiteral("observable")));
        if(shape=="call-base-after-store"){body.Remove(store);body.Insert(1,store);}
        caller.ControlFlowGraph=new(body);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[template!]),Is.EqualTo(expected));
        Assert.That(call.Operands[0],Is.SameAs(expected?ctor:baseCtor));
        Assert.That(store.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
        if(expected)Assert.That(call.Operands[2],Is.SameAs(argument));
    }
}
