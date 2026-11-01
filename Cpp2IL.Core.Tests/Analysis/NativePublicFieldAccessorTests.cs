using System;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativePublicFieldAccessorTests
{
    private static (InjectedTypeAnalysisContext Owner,FieldAnalysisContext Field,InjectedMethodAnalysisContext Getter,InjectedMethodAnalysisContext Caller) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","AccessorOwner",t.SystemObjectType,TypeAttributes.Public);
        var callerType=new InjectedTypeAnalysisContext(owner.DeclaringAssembly,"Test","AccessorConsumer",t.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("value",t.SystemInt32Type,FieldAttributes.Private);field.Offset=16;
        var getter=owner.InjectMethodContext("ReadValue",t.SystemInt32Type,MethodAttributes.Public,[]);
        var caller=new InjectedMethodAnalysisContext(callerType,"Read",t.SystemInt32Type,MethodAttributes.Public|MethodAttributes.Static,[]);
        return(owner,field,getter,caller);
    }

    [TestCase("exact",true)]
    [TestCase("wrong-width",false)]
    [TestCase("wrong-base",false)]
    [TestCase("wrong-result",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("partial",false)]
    [TestCase("longer",false)]
    [TestCase("not-return",false)]
    [TestCase("store",false)]
    [TestCase("static",false)]
    [TestCase("private",false)]
    [TestCase("virtual",false)]
    [TestCase("wrong-type",false)]
    [TestCase("wrong-owner",false)]
    [TestCase("static-field",false)]
    public void OnlyCompleteTypedPublicNonvirtualExactFieldAccessorsAreBound(string shape,bool expected)
    {
        var f=Fixture();var code=Convert.FromHexString("001040b9c0035fd6");
        if(shape=="wrong-width")code=Convert.FromHexString("000840f9c0035fd6");
        if(shape=="wrong-base")code[0]=0x20;
        if(shape=="wrong-result")code[0]=1;
        if(shape=="wrong-offset")code[1]=0x14;
        if(shape=="partial")code=code[..4];
        if(shape=="longer")code=[..code,0,0,0,0];
        if(shape=="not-return")code[4]=0;
        if(shape=="store")code[2]=0;
        if(shape=="static")f.Getter.Attributes|=MethodAttributes.Static;
        if(shape=="private")f.Getter.Attributes=MethodAttributes.Private;
        if(shape=="virtual")f.Getter.Attributes|=MethodAttributes.Virtual;
        var target=shape=="wrong-type"?f.Owner.InjectMethodContext("WrongType",f.Caller.AppContext.SystemTypes.SystemUInt32Type,MethodAttributes.Public,[]):f.Getter;
        var field=shape=="wrong-owner"?((InjectedTypeAnalysisContext)f.Caller.DeclaringType!).InjectFieldContext("other",f.Field.FieldType,FieldAttributes.Private):f.Field;
        if(shape=="static-field")field.Attributes|=FieldAttributes.Static;
        Assert.That(NativePublicFieldAccessorRecovery.TryContract(target,field,code,out var width),Is.EqualTo(expected));
        Assert.That(width,Is.EqualTo(expected?4:0));
    }

    [TestCase("read",true)]
    [TestCase("derived-receiver",true)]
    [TestCase("store",false)]
    [TestCase("nested",false)]
    [TestCase("partial",false)]
    [TestCase("unknown-width",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("unknown-receiver",false)]
    [TestCase("wrong-receiver",false)]
    [TestCase("byref",false)]
    [TestCase("self-owner",false)]
    [TestCase("missing-proof",false)]
    [TestCase("contradictory-write",false)]
    public void ProvenReadBecomesANullCheckedCallWithoutChangingStorageOperations(string shape,bool expected)
    {
        var f=Fixture();var app=f.Caller.AppContext;
        TypeAnalysisContext? receiverType=shape=="unknown-receiver"?null:shape=="wrong-receiver"?f.Caller.DeclaringType:
            shape=="byref"?new ByRefTypeAnalysisContext(f.Owner):shape=="derived-receiver"?
                new InjectedTypeAnalysisContext(f.Owner.DeclaringAssembly,"Test","DerivedAccessor",f.Owner,TypeAttributes.Public):f.Owner;
        var receiver=new LocalVariable("obj",new Register(null,"obj"),receiverType);
        var result=new LocalVariable("value",new Register(null,"result"),f.Field.FieldType);
        var field=new FieldReference(f.Field,receiver,shape=="wrong-offset"?20:16);
        if(shape=="nested")field.Parent=new FieldReference(f.Field,receiver,16);
        var instruction=shape=="store"?new Instruction(0,OpCode.Move,field,result){NativeWriteSize=4}:
            new Instruction(0,OpCode.Move,result,field){NativeReadSize=shape=="partial"?2:shape=="unknown-width"?0:4};
        if(shape=="contradictory-write")instruction.NativeWriteSize=4;
        var method=shape=="self-owner"?new InjectedMethodAnalysisContext(f.Owner,"SameOwner",f.Field.FieldType,MethodAttributes.Public,[]):f.Caller;
        method.ControlFlowGraph=new([instruction,new(1,OpCode.Return,result)]);method.Locals=[receiver,result];method.ParameterLocals=[receiver];
        var catalog=new Dictionary<FieldAnalysisContext,NativePublicFieldAccessorRecovery.Contract>();
        if(shape!="missing-proof")catalog[f.Field]=new(f.Getter,4);
        Assert.That(NativePublicFieldAccessorRecovery.Recover(method,catalog),Is.EqualTo(expected?1:0));
        Assert.That(instruction.OpCode,Is.EqualTo(expected?OpCode.Call:OpCode.Move));
        if(!expected)return;
        Assert.That(instruction.Operands[0],Is.SameAs(f.Getter));Assert.That(instruction.Operands[1],Is.SameAs(result));
        Assert.That(instruction.Operands[2],Is.SameAs(receiver));Assert.That(instruction.Operands.Count,Is.EqualTo(3));
        Assert.That(instruction.NativeNullCheckedCall,Is.True);Assert.That(instruction.NativeVirtualDispatch,Is.False);
        Assert.That(instruction.NativeReadSize,Is.Zero);
    }
}
