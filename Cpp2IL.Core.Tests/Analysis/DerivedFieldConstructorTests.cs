using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DerivedFieldConstructorTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    static (InjectedTypeAnalysisContext Owner,InjectedMethodAnalysisContext Ctor,MethodAnalysisContext Parent,
        FieldAnalysisContext A,FieldAnalysisContext B) Fixture()
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var parent=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","ParentWithEffects",t.SystemObjectType,TypeAttributes.Public);
        var parentCtor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public);
        // The parent is deliberately NOT a no-op. Its complete invocation must
        // remain at the same execution point, not be discarded or moved.
        parentCtor.ControlFlowGraph=new([new(0,OpCode.CallVoid,new StringLiteral("observable parent callback")),new(1,OpCode.Return)]);
        var owner=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","WithFields",parent,TypeAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemInt32Type,t.SystemStringType);
        var a=owner.InjectFieldContext("a",t.SystemInt32Type,FieldAttributes.Public);
        var b=owner.InjectFieldContext("b",t.SystemStringType,FieldAttributes.Public);
        var self=Local("this",owner);self.IsThis=true;
        var x=Local("x",t.SystemInt32Type);var y=Local("y",t.SystemStringType);
        ctor.ParameterLocals=[self,x,y];
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,parentCtor,self),
            new(1,OpCode.Move,new FieldReference(a,self,24),x),
            new(2,OpCode.Move,new FieldReference(b,self,32),y),new(3,OpCode.Return)]);
        return(owner,ctor,parentCtor,a,b);
    }

    [Test]
    public void CompleteDerivedTemplatePreservesTheExactObservableParentCall()
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        Assert.That(template,Is.Not.Null);Assert.That(template.BaseConstructor,Is.SameAs(f.Parent));
        var caller=f.Owner.InjectMethodContext("Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static);
        var obj=Local("obj",f.Owner);var allocation=new Instruction(0,OpCode.Newobj,obj,f.Owner);
        var parentCall=new Instruction(1,OpCode.CallVoid,f.Parent,obj);
        var a=new Instruction(2,OpCode.Move,new FieldReference(f.A,obj,24),new Immediate(42));
        var b=new Instruction(3,OpCode.Move,new FieldReference(f.B,obj,32),new StringLiteral("literal"));
        caller.ControlFlowGraph=new([allocation,parentCall,a,b,new(4,OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[template]),Is.True);
        Assert.That(parentCall.Operands[0],Is.SameAs(f.Ctor));
        Assert.That(((Immediate)parentCall.Operands[2]).Value,Is.EqualTo(42));
        Assert.That(a.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(b.OpCode,Is.EqualTo(OpCode.Nop));
        Assert.That(f.Parent.ControlFlowGraph!.Instructions.Any(i=>i.IsCall),Is.True);
    }

    [TestCase("before-parent")]
    [TestCase("missing-parent")]
    [TestCase("second-parent")]
    [TestCase("callback")]
    [TestCase("fake-this")]
    [TestCase("virtual")]
    public void PartialUnorderedOrUnboundConstructorCannotBecomeATemplate(string shape)
    {
        var f=Fixture();var all=f.Ctor.ControlFlowGraph!.Instructions;
        var call=all.Single(i=>i.IsCall);var stores=all.Where(i=>i.OpCode==OpCode.Move).ToList();
        if(shape=="before-parent")f.Ctor.ControlFlowGraph=new([stores[0],call,stores[1],new(4,OpCode.Return)]);
        if(shape=="missing-parent"){call.OpCode=OpCode.Nop;call.SetOperands();}
        if(shape=="second-parent")f.Ctor.ControlFlowGraph=new([call,new(7,OpCode.CallVoid,f.Parent,f.Ctor.ParameterLocals[0]),..stores,new(8,OpCode.Return)]);
        if(shape=="callback")f.Ctor.ControlFlowGraph=new([call,new(7,OpCode.CallVoid,new StringLiteral("callback")),..stores,new(8,OpCode.Return)]);
        if(shape=="fake-this")call.SetOperand(1,new LocalVariable("fake",new Register(null,"fake"),f.Owner){IsThis=true});
        if(shape=="virtual")call.NativeVirtualDispatch=true;
        Assert.That(InlinedConstructorRecovery.Extract(f.Ctor),Is.Null);
    }

    [TestCase("field-read")]
    [TestCase("reordered-stores")]
    [TestCase("different-parent")]
    [TestCase("callback")]
    [TestCase("late-value")]
    [TestCase("ambiguous")]
    public void CallsiteCannotMoveReadsEffectsOrGuessAnOverload(string shape)
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=f.Owner.InjectMethodContext("Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static);
        var self=Local("this",f.Owner);self.IsThis=true;caller.ParameterLocals=[self];
        var obj=Local("obj",f.Owner);var late=Local("late",f.A.FieldType);
        var allocation=new Instruction(0,OpCode.Newobj,obj,f.Owner);
        var parentCall=new Instruction(1,OpCode.CallVoid,f.Parent,obj);
        IOperand value=shape=="field-read"?new FieldReference(f.A,self,24):shape=="late-value"?late:new Immediate(42);
        var a=new Instruction(2,OpCode.Move,new FieldReference(f.A,obj,24),value);
        var b=new Instruction(3,OpCode.Move,new FieldReference(f.B,obj,32),new StringLiteral("literal"));
        var all=new List<Instruction>{allocation,parentCall};
        if(shape=="callback")all.Add(new(8,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape=="late-value")all.Add(new(8,OpCode.Move,late,new Immediate(42)));
        if(shape=="different-parent")parentCall.SetOperand(0,f.Owner.InjectMethodContext(".ctor",f.Ctor.ReturnType,MethodAttributes.Public));
        if(shape=="reordered-stores")all.AddRange([b,a]);else all.AddRange([a,b]);
        all.Add(new(9,OpCode.Return));caller.ControlFlowGraph=new(all);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template,template]:[template]),Is.False);
        Assert.That(a.OpCode,Is.EqualTo(OpCode.Move));Assert.That(b.OpCode,Is.EqualTo(OpCode.Move));
    }
}
