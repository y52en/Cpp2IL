using System;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ScalarFieldSetterArgumentTests
{
    [TestCase("int32", true)]
    [TestCase("single", true)]
    [TestCase("double", true)]
    [TestCase("int64", true)]
    [TestCase("self-field", true)]
    [TestCase("other-receiver", false)]
    [TestCase("nested", false)]
    [TestCase("source-offset", false)]
    [TestCase("destination-offset", false)]
    [TestCase("disabled", false)]
    [TestCase("readonly-source", false)]
    [TestCase("readonly-destination", false)]
    [TestCase("reference", false)]
    [TestCase("read-width", false)]
    [TestCase("write-width", false)]
    [TestCase("multiple-stores", false)]
    [TestCase("class-initializer", false)]
    [TestCase("finalizer", false)]
    [TestCase("ambiguous", false)]
    [TestCase("type-mismatch", false)]
    public void OnlyOneExactSameReceiverScalarReadMayBecomeSingleSetterArgument(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","FieldSetter",types.SystemObjectType,TypeAttributes.Public);
        var scalar=shape switch {"single"=>types.SystemSingleType,"double"=>types.SystemDoubleType,
            "int64"=>types.SystemInt64Type,"reference"=>types.SystemObjectType,_=>types.SystemInt32Type};
        var width=shape is "double" or "int64" or "reference"?8:4;
        var destination=owner.InjectFieldContext("destination",scalar,FieldAttributes.Private|(shape=="readonly-destination"?FieldAttributes.InitOnly:0));destination.Offset=16;
        var source=owner.InjectFieldContext("source",shape=="type-mismatch"?types.SystemSingleType:scalar,FieldAttributes.Private|(shape=="readonly-source"?FieldAttributes.InitOnly:0));source.Offset=24;
        var setter=owner.InjectMethodContext("Setter",types.SystemVoidType,MethodAttributes.Public,scalar);
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};
        var argument=new LocalVariable("argument",new Register(null,"p"),scalar);setter.ParameterLocals=[self,argument];
        var stores=new List<Instruction>{new(0,OpCode.Move,new FieldReference(destination,self,16),argument){NativeWriteSize=width}};
        if(shape=="multiple-stores")stores.Add(new(1,OpCode.Move,new FieldReference(source,self,24),argument){NativeWriteSize=width});
        stores.Add(new(2,OpCode.Return));setter.ControlFlowGraph=new(stores);
        var template=InlinedFieldMethodRecovery.Extract(setter);Assert.That(template,Is.Not.Null);
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey,shape=="ambiguous"?new[]{template!,template!}:new[]{template!});
        if(shape=="class-initializer")owner.InjectMethodContext(".cctor",types.SystemVoidType,MethodAttributes.Static);
        if(shape=="finalizer")owner.InjectMethodContext("Finalize",types.SystemVoidType,MethodAttributes.Family);
        var caller=owner.InjectMethodContext("Caller",types.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var receiver=new LocalVariable("receiver",new Register(null,"obj"),owner);
        var readReceiver=shape=="other-receiver"?new LocalVariable("other",new Register(null,"other"),owner):receiver;
        var readField=shape=="self-field"?destination:source;
        var read=new FieldReference(readField,readReceiver,readField.Offset+(shape=="source-offset"?1:0));
        if(shape=="nested")read.Parent=new FieldReference(source,receiver,source.Offset);
        var write=new Instruction(5,OpCode.Move,new FieldReference(destination,receiver,destination.Offset+(shape=="destination-offset"?1:0)),read)
            {NativeWriteSize=shape=="write-width"?width*2:width,NativeReadSize=shape=="read-width"?width*2:width};
        var instructions=new List<Instruction>{write};
        if(shape=="multiple-stores")instructions.Add(new(6,OpCode.Move,new FieldReference(source,receiver,source.Offset),read){NativeWriteSize=width});
        instructions.Add(new(7,OpCode.Return));caller.ControlFlowGraph=new(instructions);
        Assert.That(InlinedFieldMethodRecovery.Recover(caller,shape!="disabled"),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(write.OpCode,Is.EqualTo(OpCode.CallVoid));
            Assert.That(write.Operands,Is.EqualTo(new IOperand[]{setter,receiver,read}));
            Assert.That(write.Operands[2],Is.SameAs(read),"read must stay at original store point");
        }
        else
        {
            Assert.That(write.OpCode,Is.EqualTo(OpCode.Move));
            Assert.That(write.Operands[1],Is.SameAs(read));
        }
    }
}
