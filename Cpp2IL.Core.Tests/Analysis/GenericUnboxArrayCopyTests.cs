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

public class GenericUnboxArrayCopyTests
{
    static (InjectedMethodAnalysisContext Method,Instruction Call,LocalVariable Array,
        Instruction[] Loads,Instruction[] Stores,Instruction NullJump,Instruction BoundsJump) Shape(int size,int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Fixture","ArrayHolder",
            app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var t=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner);
        owner.GenericParameters.Add(t);var arrayType=new SzArrayTypeAnalysisContext(t);
        var field=owner.InjectFieldContext("Items",arrayType,FieldAttributes.Public);
        var method=owner.InjectMethodContext("Set",app.SystemTypes.SystemVoidType,MethodAttributes.Public,app.SystemTypes.SystemObjectType);
        var self=new LocalVariable("this",new Register(null,"this"),owner){IsThis=true};
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var array=new LocalVariable("array",new Register(null,"array"),arrayType);
        var pointer=new LocalVariable("pointer",new Register(null,"pointer"));
        var nullCondition=new LocalVariable("null",new Register(null,"null"),app.SystemTypes.SystemBooleanType);
        var length=new LocalVariable("length",new Register(null,"length"),app.SystemTypes.SystemInt32Type);
        var boundsCondition=new LocalVariable("empty",new Register(null,"empty"),app.SystemTypes.SystemBooleanType);
        var nullThrow=new Instruction(80,OpCode.Throw,owner.DeclaringAssembly.GetTypeByFullName("System.NullReferenceException")!);
        var boundsThrow=new Instruction(70,OpCode.Throw,owner.DeclaringAssembly.GetTypeByFullName("System.IndexOutOfRangeException")!);
        var nullJump=new Instruction(2,OpCode.ConditionalJump,nullThrow,nullCondition);
        var call=new Instruction(3,OpCode.Call,new Immediate(0xA61E70),pointer,value,
            new RuntimeClassTypeAnalysisContext(t,owner.DeclaringAssembly));
        var instructions=new List<Instruction>{new(0,OpCode.Move,array,new FieldReference(field,self,32)),
            new(1,OpCode.CheckEqual,nullCondition,array,new Immediate(0)),nullJump,call,
            new(4,OpCode.Move,length,new ArrayLength(array))};
        var locals=new List<LocalVariable>{self,value,array,pointer,nullCondition,length,boundsCondition};
        var loads=new List<Instruction>();var stores=new List<Instruction>();
        for(var offset=0;offset<size;offset+=width)
        {
            var chunk=new LocalVariable("part"+offset,new Register(null,"part"+offset));locals.Add(chunk);
            var load=new Instruction(instructions.Count,OpCode.Move,chunk,new MemoryOperand(pointer,addend:offset)){NativeReadSize=width};
            loads.Add(load);instructions.Add(load);
            stores.Add(new(30+offset,OpCode.Move,offset==0?new ArrayAccess(array,new Immediate(0)):
                new MemoryOperand(array,addend:32+offset),chunk){NativeWriteSize=width});
        }
        instructions.Add(new(20,OpCode.CheckEqual,boundsCondition,length,new Immediate(0)));
        var boundsJump=new Instruction(21,OpCode.ConditionalJump,boundsThrow,boundsCondition);instructions.Add(boundsJump);
        instructions.AddRange(stores);instructions.Add(new(69,OpCode.Return));
        instructions.Add(boundsThrow);instructions.Add(new(71,OpCode.Return));instructions.Add(nullThrow);instructions.Add(new(81,OpCode.Return));
        method.ControlFlowGraph=new ISILControlFlowGraph(instructions);
        method.ParameterLocals=[self,value];method.Locals=locals;method.AnalysisWarnings=[];
        return (method,call,array,loads.ToArray(),stores.ToArray(),nullJump,boundsJump);
    }

    [TestCase(4,4)]
    [TestCase(8,4)]
    [TestCase(8,8)]
    [TestCase(12,4)]
    [TestCase(16,8)]
    [TestCase(16,16)]
    public void CompleteFirstElementCopiesPreserveNullAndBoundsBranchesAndConversionPosition(int size,int width)
    {
        var s=Shape(size,width);var index=s.Call.Index;
        var checks=s.Method.ControlFlowGraph!.Instructions.Where(i=>i.OpCode is OpCode.ConditionalJump or OpCode.Throw)
            .Select(i=>i.ToString()).ToArray();
        Assert.That(GenericUnboxArrayCopyRecovery.Rewrite(s.Method,_=>size),Is.True);
        Assert.That(s.Call.OpCode,Is.EqualTo(OpCode.UnboxAny));Assert.That(s.Call.Index,Is.EqualTo(index));
        Assert.That(s.Method.ControlFlowGraph.Instructions.Where(i=>i.OpCode is OpCode.ConditionalJump or OpCode.Throw)
            .Select(i=>i.ToString()),Is.EqualTo(checks));
        Assert.That(s.Stores[0].OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(s.Stores[0].Operands[0],Is.TypeOf<ArrayAccess>());
        Assert.That(s.Stores[0].Operands[1],Is.SameAs(s.Call.Destination));
        Assert.That(s.Loads.All(i=>i.OpCode==OpCode.Nop),Is.True);
        Assert.That(s.Stores.Skip(1).All(i=>i.OpCode==OpCode.Nop),Is.True);
    }

    [TestCase("partial")]
    [TestCase("overlap")]
    [TestCase("wrong-array")]
    [TestCase("dynamic-index")]
    [TestCase("nonzero-index")]
    [TestCase("wrong-header")]
    [TestCase("width")]
    [TestCase("extra-call")]
    [TestCase("pointer-escape")]
    [TestCase("chunk-escape")]
    [TestCase("unknown-size")]
    [TestCase("oversize")]
    [TestCase("static")]
    [TestCase("nonvoid")]
    [TestCase("wrong-helper")]
    [TestCase("typed-pointer")]
    [TestCase("unknown-handle")]
    public void UnprovedOrPartialCopiesDoNotMutateAnyInstruction(string change)
    {
        var s=Shape(8,4);var graph=s.Method.ControlFlowGraph!;
        if(change=="partial")graph.Blocks.Single(b=>b.Instructions.Contains(s.Stores[1])).Instructions.Remove(s.Stores[1]);
        if(change=="overlap")s.Loads[1].SetOperand(1,s.Loads[0].Operands[1]);
        if(change=="wrong-array")s.Stores[1].SetOperand(0,new MemoryOperand(new LocalVariable("other",new Register(null,"other")),addend:36));
        if(change=="dynamic-index")((ArrayAccess)s.Stores[0].Operands[0]).Index=new LocalVariable("index",new Register(null,"index"));
        if(change=="nonzero-index")((ArrayAccess)s.Stores[0].Operands[0]).Index=new Immediate(1);
        if(change=="wrong-header")s.Stores[1].SetOperand(0,new MemoryOperand(s.Array,addend:28));
        if(change=="width")s.Stores[1].NativeWriteSize=8;
        var block=graph.Blocks.Single(b=>b.Instructions.Contains(s.Call));
        if(change=="extra-call")block.Instructions.Insert(block.Instructions.IndexOf(s.Call)+1,new(90,OpCode.CallVoid,new Immediate(123)));
        if(change is "pointer-escape" or "chunk-escape")block.Instructions.Add(new(90,OpCode.Move,
            new LocalVariable("alias",new Register(null,"alias")),change=="pointer-escape"?s.Call.Destination!:s.Loads[0].Destination!));
        if(change=="static")s.Method.Attributes|=MethodAttributes.Static;
        if(change=="nonvoid")s.Method.OverrideReturnType=s.Method.AppContext.SystemTypes.SystemInt32Type;
        if(change=="wrong-helper")s.Call.SetOperand(0,new Immediate(0xA61E74));
        if(change=="typed-pointer")((LocalVariable)s.Call.Destination!).Type=s.Method.AppContext.SystemTypes.SystemIntPtrType;
        if(change=="unknown-handle")s.Call.SetOperand(3,new Immediate(0));
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(GenericUnboxArrayCopyRecovery.Rewrite(s.Method,_=>change=="unknown-size"?null:change=="oversize"?128:8),Is.False);
        Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
    }

    [Test]
    public void UnrelatedImageCannotActivateNativeProfile()
    {
        var s=Shape(8,4);Assert.That(GenericUnboxArrayCopyRecovery.Run(s.Method),Is.False);
    }
}
