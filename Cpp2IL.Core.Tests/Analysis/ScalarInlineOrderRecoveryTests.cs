using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ScalarInlineOrderRecoveryTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("ordered",true)]
    [TestCase("reversed",true)]
    [TestCase("rotate",true)]
    [TestCase("reorder-disabled",false)]
    [TestCase("wrong-helper-width",false)]
    [TestCase("wrong-caller-width",false)]
    [TestCase("unknown-helper-width",false)]
    [TestCase("unknown-caller-width",false)]
    [TestCase("overlap",false)]
    [TestCase("header",false)]
    [TestCase("reference-field",false)]
    [TestCase("readonly-field",false)]
    [TestCase("explicit-layout",false)]
    [TestCase("class-initializer",false)]
    [TestCase("finalizer",false)]
    [TestCase("duplicate-actual",false)]
    [TestCase("different-receiver",false)]
    [TestCase("interior-field-offset",false)]
    [TestCase("side-effect",false)]
    [TestCase("ambiguous",false)]
    public void OnlyIndependentScalarWritesCanCommute(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","ScalarOwner",t.SystemObjectType,
            TypeAttributes.Public|(shape=="explicit-layout"?TypeAttributes.ExplicitLayout:0));
        var valueType=shape=="reference-field"?t.SystemObjectType:t.SystemSingleType;
        var helper=owner.InjectMethodContext("SetAll",t.SystemVoidType,MethodAttributes.Public,t.SystemInt32Type,valueType,t.SystemBooleanType);
        var a=owner.InjectFieldContext("a",t.SystemInt32Type,FieldAttributes.Private);a.Offset=shape=="header"?8:16;
        var b=owner.InjectFieldContext("b",valueType,FieldAttributes.Private|(shape=="readonly-field"?FieldAttributes.InitOnly:0));b.Offset=shape=="overlap"?16:20;
        var c=owner.InjectFieldContext("c",t.SystemBooleanType,FieldAttributes.Private);c.Offset=24;
        var self=Local("this",owner);self.IsThis=true;
        var p=Local("p",t.SystemInt32Type);var q=Local("q",valueType);var r=Local("r",t.SystemBooleanType);
        helper.ParameterLocals=[self,p,q,r];
        var first=new Instruction(0,OpCode.Move,new FieldReference(a,self,a.Offset),p)
            {NativeWriteSize=shape=="wrong-helper-width"?8:shape=="unknown-helper-width"?0:4};
        helper.ControlFlowGraph=new([first,
            new(1,OpCode.Move,new FieldReference(b,self,b.Offset),q){NativeWriteSize=shape=="reference-field"?8:4},
            new(2,OpCode.Move,new FieldReference(c,self,c.Offset),r){NativeWriteSize=1},new(3,OpCode.Return)]);
        var template=InlinedFieldMethodRecovery.Extract(helper);Assert.That(template,Is.Not.Null);
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey,shape=="ambiguous"?new[]{template!,template!}:new[]{template!});
        if(shape=="class-initializer")owner.InjectMethodContext(".cctor",t.SystemVoidType,MethodAttributes.Static);
        if(shape=="finalizer")owner.InjectMethodContext("Finalize",t.SystemVoidType,MethodAttributes.Family);
        var caller=owner.InjectMethodContext("Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var obj=Local("obj",owner);var other=Local("other",owner);
        IOperand qValue=shape=="reference-field"?Local("reference",t.SystemObjectType):new FloatLiteral(1.25f);
        var actualA=new Instruction(5,OpCode.Move,new FieldReference(a,obj,a.Offset),new Immediate(17)){NativeWriteSize=4};
        var actualB=new Instruction(6,OpCode.Move,new FieldReference(b,shape=="different-receiver"?other:obj,
            shape=="interior-field-offset"?b.Offset+1:b.Offset),qValue)
            {NativeWriteSize=shape=="wrong-caller-width"?8:shape=="unknown-caller-width"?0:4};
        var actualC=new Instruction(7,OpCode.Move,new FieldReference(c,obj,c.Offset),new Immediate(1)){NativeWriteSize=1};
        var stores=shape=="ordered"?new[]{actualA,actualB,actualC}:
            shape=="rotate"?new[]{actualB,actualC,actualA}:new[]{actualC,actualB,actualA};
        if(shape=="duplicate-actual")stores[1]=new(8,OpCode.Move,new FieldReference(c,obj,c.Offset),new Immediate(1)){NativeWriteSize=1};
        var instructions=new List<Instruction>(stores);
        if(shape=="side-effect")instructions.Insert(1,new(9,OpCode.CallVoid,new StringLiteral("effect")));
        instructions.Add(new(10,OpCode.Return));caller.ControlFlowGraph=new(instructions);
        var previous=instructions.ToDictionary(i=>i,i=>(i.OpCode,Args:i.Operands.ToArray()));
        Assert.That(InlinedFieldMethodRecovery.Recover(caller,shape!="reorder-disabled"),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(stores[0].OpCode,Is.EqualTo(OpCode.CallVoid));
            Assert.That(stores[0].Operands,Is.EqualTo(new IOperand[]{helper,obj,new Immediate(17),qValue,new Immediate(1)}));
            Assert.That(stores.Skip(1).All(i=>i.OpCode==OpCode.Nop),Is.True);
        }
        else foreach(var instruction in instructions)
        {
            Assert.That(instruction.OpCode,Is.EqualTo(previous[instruction].OpCode));
            Assert.That(instruction.Operands,Is.EqualTo(previous[instruction].Args));
        }
    }

    [TestCase("single-zero",true)]
    [TestCase("single-nonzero",true)]
    [TestCase("single-negative-zero",true)]
    [TestCase("double-zero",true)]
    [TestCase("double-nonzero",true)]
    [TestCase("opposite-zero-sign",false)]
    [TestCase("different-nan-payload",false)]
    [TestCase("wrong-register-bank",false)]
    public void FloatingResetTemplatesPreserveExactNativeBits(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","FloatReset",t.SystemObjectType,TypeAttributes.Public);
        var type=shape.StartsWith("double")?t.SystemDoubleType:t.SystemSingleType;
        var field=owner.InjectFieldContext("value",type,FieldAttributes.Private);field.Offset=16;
        var helper=owner.InjectMethodContext("Reset",t.SystemVoidType,MethodAttributes.Public);
        var self=Local("this",owner);self.IsThis=true;helper.ParameterLocals=[self];
        IOperand value=shape switch {
            "single-nonzero"=>new FloatLiteral(1.5f),"single-negative-zero" or "opposite-zero-sign"=>new FloatLiteral(-0f),
            "double-zero"=>new DoubleLiteral(0d),"double-nonzero"=>new DoubleLiteral(-2.25d),
            "different-nan-payload"=>new FloatLiteral(BitConverter.Int32BitsToSingle(0x7fc00001)),_=>new FloatLiteral(0f)};
        helper.ControlFlowGraph=new([new(0,OpCode.Move,new FieldReference(field,self,16),value){NativeWriteSize=type==t.SystemDoubleType?8:4},new(1,OpCode.Return)]);
        var template=InlinedFieldMethodRecovery.Extract(helper);Assert.That(template,Is.Not.Null);
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey,new[]{template!});
        var caller=owner.InjectMethodContext("Caller",t.SystemVoidType,MethodAttributes.Static);var obj=Local("obj",owner);
        IOperand actual=shape switch {
            "opposite-zero-sign"=>new FloatLiteral(0f),
            "different-nan-payload"=>new FloatLiteral(BitConverter.Int32BitsToSingle(0x7fc00002)),
            "wrong-register-bank"=>new DoubleLiteral(0d),_=>value};
        var store=new Instruction(2,OpCode.Move,new FieldReference(field,obj,16),actual){NativeWriteSize=type==t.SystemDoubleType?8:4};
        caller.ControlFlowGraph=new([store,new(3,OpCode.Return)]);
        Assert.That(InlinedFieldMethodRecovery.Recover(caller,true),Is.EqualTo(expected?1:0));
        Assert.That(store.OpCode,Is.EqualTo(expected?OpCode.CallVoid:OpCode.Move));
    }

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(8)]
    public void FloatingTemplateRequiresTheExactNativeStoreWidth(int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","UnknownFloat",t.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("value",t.SystemSingleType,FieldAttributes.Private);field.Offset=16;
        var helper=owner.InjectMethodContext("Reset",t.SystemVoidType,MethodAttributes.Public);
        var self=Local("this",owner);self.IsThis=true;helper.ParameterLocals=[self];
        helper.ControlFlowGraph=new([new(0,OpCode.Move,new FieldReference(field,self,16),new FloatLiteral(0f)){NativeWriteSize=width},new(1,OpCode.Return)]);
        Assert.That(InlinedFieldMethodRecovery.Extract(helper),Is.Null);
    }
}
