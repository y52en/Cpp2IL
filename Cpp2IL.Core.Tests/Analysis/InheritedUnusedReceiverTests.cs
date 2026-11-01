using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InheritedUnusedReceiverTests
{
    [TestCase("ancestor",true)] [TestCase("same-owner",true)] [TestCase("public",true)]
    [TestCase("protected-internal",true)] [TestCase("unrelated",false)] [TestCase("private",false)]
    [TestCase("constructor",false)] [TestCase("virtual",false)] [TestCase("virtual-dispatch",false)]
    [TestCase("static-target",false)] [TestCase("static-caller",false)] [TestCase("missing-self",false)]
    [TestCase("wrong-self-type",false)] [TestCase("unproven",false)] [TestCase("already-self",false)]
    [TestCase("multiple-self",false)] [TestCase("returning",true)]
    public void OnlyExactMetadataAncestorWithAnUnusedNativeReceiverMayUseExistingThis(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var assembly=t.SystemObjectType.DeclaringAssembly;
        var parent=new InjectedTypeAnalysisContext(assembly,"Test","ReceiverBase",t.SystemObjectType,TypeAttributes.Public);
        var middle=new InjectedTypeAnalysisContext(assembly,"Test","ReceiverMiddle",parent,TypeAttributes.Public);
        var child=new InjectedTypeAnalysisContext(assembly,"Test","ReceiverChild",middle,TypeAttributes.Public);
        var unrelated=new InjectedTypeAnalysisContext(assembly,"Test","OtherReceiver",t.SystemObjectType,TypeAttributes.Public);
        var targetOwner=shape=="same-owner"?child:shape=="unrelated"?unrelated:parent;
        var attributes=shape=="private"?MethodAttributes.Private:shape=="public"?MethodAttributes.Public:
            shape=="protected-internal"?MethodAttributes.FamORAssem:MethodAttributes.Family;
        if(shape=="virtual")attributes|=MethodAttributes.Virtual;
        if(shape=="static-target")attributes|=MethodAttributes.Static;
        var target=new InjectedMethodAnalysisContext(targetOwner,shape=="constructor"?".ctor":"IgnoreReceiver",
            shape=="returning"?t.SystemInt32Type:t.SystemVoidType,attributes,[]);
        var self=new LocalVariable("this",new Register(0,"X0"),shape=="wrong-self-type"?unrelated:child){IsThis=true};
        var wrong=new LocalVariable("length",new Register(0,"X0",1),t.SystemInt32Type);
        var arg=new LocalVariable("arg",new Register(1,"X1"),t.SystemInt32Type);
        var result=new LocalVariable("result",new Register(0,"X0",2),t.SystemInt32Type);
        var receiver=shape=="already-self"?self:wrong;
        var call=shape=="returning"?new Instruction(0,OpCode.Call,target,result,receiver,arg):new Instruction(0,OpCode.CallVoid,target,receiver,arg);
        call.NativeVirtualDispatch=shape=="virtual-dispatch";call.NativeNullCheckedCall=true;
        var caller=new InjectedMethodAnalysisContext(child,"Caller",t.SystemVoidType,
            MethodAttributes.Public|(shape=="static-caller"?MethodAttributes.Static:0),[])
        {
            ControlFlowGraph=new([call,new(1,OpCode.Return)]),Locals=[wrong,arg,result],
            ParameterLocals=shape=="missing-self"?[]:shape=="multiple-self"?[self,new LocalVariable("other",new Register(2,"X2"),child){IsThis=true}]:[self]
        };
        var proofCalls=0;
        Assert.That(UnusedInstanceReceiverRecovery.Recover(caller,_=>{proofCalls++;return shape!="unproven";}),Is.EqualTo(expected?1:0));
        Assert.That(call.Operands[shape=="returning"?2:1],Is.SameAs(expected?self:receiver));
        Assert.That(call.Operands[^1],Is.SameAs(arg));Assert.That(call.NativeNullCheckedCall,Is.True);
        Assert.That(proofCalls,Is.EqualTo(expected || shape=="unproven"?1:0));
        if(expected)Assert.That(caller.Locals,Does.Contain(self));
    }
}
