using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericUnboxFieldCopyTests
{
    static (InjectedMethodAnalysisContext Method,Instruction Call,FieldReference Field,int Size) Shape(int size,int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Fixture","Container",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var t=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner);
        owner.GenericParameters.Add(t);
        var field=owner.InjectFieldContext("Value",t,FieldAttributes.Public);
        var method=owner.InjectMethodContext("Set",app.SystemTypes.SystemVoidType,MethodAttributes.Public,app.SystemTypes.SystemObjectType);
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var pointer=new LocalVariable("pointer",new Register(null,"pointer"));
        var target=new FieldReference(field,self,32);
        var call=new Instruction(0,OpCode.Call,new Immediate(0xA61E70),pointer,value,
            new RuntimeClassTypeAnalysisContext(t,owner.DeclaringAssembly),new Immediate(123));
        var instructions=new List<Instruction>{call};var parts=new List<LocalVariable>();
        for(var offset=0;offset<size;offset+=width)
        {
            var part=new LocalVariable("part"+offset,new Register(null,"part"+offset));parts.Add(part);
            instructions.Add(new(instructions.Count,OpCode.Move,part,new MemoryOperand(pointer,addend:offset)){NativeReadSize=width});
        }
        for(var i=0;i<parts.Count;i++)
            instructions.Add(new(instructions.Count,OpCode.Move,i==0?target:new MemoryOperand(self,addend:32+i*width),parts[i]){NativeWriteSize=width});
        instructions.Add(new(instructions.Count,OpCode.Return));
        method.ControlFlowGraph=new ISILControlFlowGraph(instructions);
        method.ParameterLocals=[self,value];method.Locals=[self,value,pointer,..parts];method.AnalysisWarnings=[];
        return (method,call,target,size);
    }

    [TestCase(4,4)]
    [TestCase(8,4)]
    [TestCase(8,8)]
    [TestCase(12,4)]
    [TestCase(16,8)]
    [TestCase(16,16)]
    [TestCase(32,16)]
    public void CompleteCopiesBecomeCheckedValueConversionAndExactlyOneWholeFieldStore(int size,int width)
    {
        var shape=Shape(size,width);var source=shape.Call.Operands[2];
        Assert.That(GenericUnboxFieldCopyRecovery.Rewrite(shape.Method,(_,f)=>ReferenceEquals(f,shape.Field)?size:null),Is.True);
        Assert.That(shape.Call.OpCode,Is.EqualTo(OpCode.UnboxAny));
        Assert.That(shape.Call.Operands.Count,Is.EqualTo(3));
        Assert.That(shape.Call.Sources,Is.EquivalentTo(new[]{source}));
        Assert.That(((LocalVariable)shape.Call.Destination!).Type,Is.SameAs(shape.Field.Field.FieldType));
        var stores=shape.Method.ControlFlowGraph!.Instructions.Where(i=>i.OpCode==OpCode.Move).ToArray();
        Assert.That(stores.Length,Is.EqualTo(1));Assert.That(stores[0].Operands[0],Is.SameAs(shape.Field));
        Assert.That(stores[0].Operands[1],Is.SameAs(shape.Call.Destination));
    }

    [TestCase("partial")]
    [TestCase("overlap")]
    [TestCase("wrong-target")]
    [TestCase("width")]
    [TestCase("extra-call")]
    [TestCase("escape")]
    [TestCase("unproved-size")]
    [TestCase("larger-size")]
    [TestCase("typed-pointer")]
    [TestCase("static")]
    [TestCase("return-value")]
    [TestCase("wrong-helper")]
    [TestCase("unknown-handle")]
    [TestCase("field-offset")]
    public void PartialAmbiguousOrEscapingCopiesKeepEveryInstructionUnchanged(string change)
    {
        var shape=Shape(8,4);var graph=shape.Method.ControlFlowGraph!;
        Instruction Find(int index)=>graph.Instructions.Single(i=>i.Index==index);
        if(change=="partial") {var last=Find(4);graph.Blocks.Single(b=>b.Instructions.Contains(last)).Instructions.Remove(last);}
        if(change=="overlap")Find(2).SetOperand(1,new MemoryOperand((LocalVariable)shape.Call.Destination!));
        if(change=="wrong-target")Find(4).SetOperand(0,new MemoryOperand(new LocalVariable("other",new Register(null,"other")),addend:36));
        if(change=="width")Find(4).NativeWriteSize=8;
        if(change=="extra-call")graph.Blocks.Single(b=>b.Instructions.Contains(shape.Call)).Instructions.Add(
            new(88,OpCode.Call,new Immediate(1234),new LocalVariable("result",new Register(null,"result"))));
        if(change=="escape") {var first=Find(3);var list=graph.Blocks.Single(b=>b.Instructions.Contains(first)).Instructions;
            list.Insert(list.IndexOf(first),new(88,OpCode.Move,new LocalVariable("alias",new Register(null,"alias")),shape.Call.Destination!));}
        if(change=="typed-pointer")((LocalVariable)shape.Call.Destination!).Type=shape.Method.AppContext.SystemTypes.SystemIntPtrType;
        if(change=="static")shape.Method.Attributes|=MethodAttributes.Static;
        if(change=="return-value")shape.Method.OverrideReturnType=shape.Method.AppContext.SystemTypes.SystemInt32Type;
        if(change=="wrong-helper")shape.Call.SetOperand(0,new Immediate(0xA61E74));
        if(change=="unknown-handle")shape.Call.SetOperand(3,new LocalVariable("unknown",new Register(null,"unknown")));
        if(change=="field-offset")shape.Field.Offset=40;
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(GenericUnboxFieldCopyRecovery.Rewrite(shape.Method,(_,_)=>change=="unproved-size"?null:change=="larger-size"?12:8),Is.False);
        Assert.That(graph.Instructions.Select(i=>i.ToString()).ToArray(),Is.EqualTo(before));
    }

    [Test]
    public void UnrelatedNativeImageCannotUseDetachedShapeProofs()
    {
        var shape=Shape(8,4);
        Assert.That(GenericUnboxFieldCopyRecovery.Run(shape.Method),Is.False);
        Assert.That(shape.Call.OpCode,Is.EqualTo(OpCode.Call));
    }
}
