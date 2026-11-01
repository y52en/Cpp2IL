using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardedConstructorReferenceUpcastTests
{
    [TestCase("upcast",true,true)]
    [TestCase("transitive-upcast",true,true)]
    [TestCase("base-typed-argument",true,false)]
    [TestCase("unknown-argument",true,false)]
    [TestCase("null-argument",true,true)]
    [TestCase("late-argument",true,false)]
    [TestCase("downcast",false,false)]
    [TestCase("boxing",false,false)]
    [TestCase("interface",false,false)]
    [TestCase("same-name-unrelated",false,false)]
    [TestCase("cyclic-unrelated",false,false)]
    public void RequiresMetadataClassUpcastAndNarrowArgumentProof(string shape,bool extracts,bool recovers)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var assembly=t.SystemObjectType.DeclaringAssembly;
        InjectedTypeAnalysisContext Class(string name,TypeAnalysisContext parent,TypeAttributes attributes=TypeAttributes.Public)
            =>new(assembly,"UpcastTest",name,parent,attributes);
        var baseArgument=Class("BaseArgument",t.SystemObjectType);
        var derivedArgument=Class("DerivedArgument",baseArgument);
        TypeAnalysisContext declared=derivedArgument,forwarded=baseArgument;
        if(shape=="transitive-upcast")derivedArgument.OverrideBaseType=Class("Intermediate",baseArgument);
        if(shape=="downcast"){declared=baseArgument;forwarded=derivedArgument;}
        if(shape=="boxing"){declared=t.SystemInt32Type;forwarded=t.SystemObjectType;}
        if(shape=="interface")forwarded=Class("Contract",t.SystemObjectType,TypeAttributes.Public|TypeAttributes.Interface|TypeAttributes.Abstract);
        if(shape=="same-name-unrelated")forwarded=Class("BaseArgument",t.SystemObjectType);
        if(shape=="cyclic-unrelated")derivedArgument.OverrideBaseType=derivedArgument;
        var parent=Class("Parent",t.SystemObjectType);
        var owner=Class("Child",parent);
        var baseCtor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,forwarded);
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,declared);
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};
        var input=new LocalVariable("input",new Register(null,"input"),declared);
        ctor.ParameterLocals=[self,input];
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,baseCtor,self,input),new(1,OpCode.Return)]);
        var template=ForwardedConstructorRecovery.Extract(ctor);
        Assert.That(template!=null,Is.EqualTo(extracts));
        if(template==null)return;
        var method=new InjectedMethodAnalysisContext(owner,"Create",owner,MethodAttributes.Public|MethodAttributes.Static,[derivedArgument]);
        var argument=new LocalVariable("argument",new Register(null,"argument"),shape=="base-typed-argument"?baseArgument:derivedArgument);
        if(shape=="unknown-argument")argument.Type=null;
        method.ParameterLocals=[argument];
        var obj=new LocalVariable("obj",new Register(null,"obj"),owner);
        var allocation=new Instruction(10,OpCode.Newobj,obj,owner);
        IOperand actual=shape=="null-argument"?new Immediate(0):argument;
        var call=new Instruction(12,OpCode.CallVoid,baseCtor,obj,actual);
        method.ControlFlowGraph=new([allocation,call,new(13,OpCode.Return,obj)]);
        method.Locals=[argument,obj];
        if(shape=="late-argument")
            method.ControlFlowGraph.Blocks.Single(b=>b.Instructions.Contains(allocation)).Instructions.Insert(1,new(11,OpCode.Move,argument,new Immediate(0)));
        Assert.That(ForwardedConstructorRecovery.Recover(method,allocation,[template]),Is.EqualTo(recovers));
        Assert.That(call.Operands[0],Is.SameAs(recovers?ctor:baseCtor));
        Assert.That(call.Operands[2],Is.SameAs(actual));
        Assert.That(ctor.Parameters[0].ParameterType,Is.SameAs(declared));
    }
}
