using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SplitArrayAccessTests
{
    [TestCase(false,false,4,2,true)]
    [TestCase(true,false,4,2,true)]
    [TestCase(false,true,4,2,true)]
    [TestCase(false,false,8,2,false)]
    [TestCase(false,false,4,3,false)]
    public void PreserveComputedInt32IndexRatherThanMovingItsConstantIntoPointerBytes(
        bool store,bool subtract,int width,int shift,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var index=new LocalVariable("index",new Register(null,"W1"),app.SystemTypes.SystemInt32Type);
        var computed=new LocalVariable("computed",new Register(null,"W9"),app.SystemTypes.SystemInt32Type);
        var scaled=new LocalVariable("scaled",new Register(null,"TMP"));
        var address=new LocalVariable("address",new Register(null,"X8"));
        var array=new LocalVariable("array",new Register(null,"X20"),new SzArrayTypeAnalysisContext(app.SystemTypes.SystemSingleType));
        var value=new LocalVariable("value",new Register(null,"S0"),app.SystemTypes.SystemSingleType);
        var memory=new MemoryOperand(address,addend:32);
        var access=store ? new Instruction(3,OpCode.Move,memory,value){NativeWriteSize=width}
            : new Instruction(3,OpCode.Move,value,memory){NativeReadSize=width};
        var calculation=new Instruction(0,subtract?OpCode.Subtract:OpCode.Add,computed,index,new Immediate(10));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([calculation,new(1,OpCode.ShiftLeft,scaled,computed,new Immediate(shift)),
            new(2,OpCode.Add,address,array,scaled),access,new(4,OpCode.Return)]);
        Assert.That(ArrayRecovery.RecoverSplitAccesses(method),Is.EqualTo(expected));
        var result=access.Operands[store?0:1] as ArrayAccess;
        Assert.That(result!=null,Is.EqualTo(expected));
        if(result!=null) Assert.That(result.Index,Is.SameAs(computed));
        Assert.That(calculation.OpCode,Is.EqualTo(subtract?OpCode.Subtract:OpCode.Add));
        Assert.That(calculation.Operands[2],Is.TypeOf<Immediate>());
    }

    [TestCase(false,4,true)]
    [TestCase(true,4,false)]
    [TestCase(false,8,false)]
    [TestCase(false,0,false)]
    public void Int32LengthRecoveryDoesNotReinterpretHeaderStoresOrLongLength(bool store,int width,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemObjectType;
        var array=new LocalVariable("array",new Register(null,"X19"),new SzArrayTypeAnalysisContext(type));
        var value=new LocalVariable("length",new Register(null,"X0"));
        var memory=new MemoryOperand(array,addend:24);
        var access=store ? new Instruction(0,OpCode.Move,memory,value){NativeWriteSize=width}
            : new Instruction(0,OpCode.Move,value,memory){NativeReadSize=width};
        var method=new InjectedMethodAnalysisContext(type,"Length",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([access,new(1,OpCode.Return)]);
        Assert.That(ArrayRecovery.RecoverSplitAccesses(method),Is.EqualTo(expected));
        Assert.That(access.Operands[store?0:1] is ArrayLength,Is.EqualTo(expected));
        if(expected)
        {
            method.Locals=[array,value];method.ParameterLocals=[];method.AnalysisWarnings=[];
            LocalVariables.ResolveTypesAndFields(method);
            Assert.That(value.Type?.FullName,Is.EqualTo("System.Int32"));
        }
    }

    [TestCase(false,8,32,3,true)]
    [TestCase(true,8,32,3,true)]
    [TestCase(false,4,32,3,false)] // Partial reference read.
    [TestCase(false,8,24,3,false)] // Header, not elements.
    [TestCase(false,8,32,2,false)] // Wrong element stride.
    [TestCase(false,0,32,3,false)] // Unknown width cannot be treated as load.
    public void SplitNativeAddressRequiresExactWidthAndStride(bool store,int width,int header,int shift,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemObjectType;
        var array=new LocalVariable("array",new Register(null,"X19"),new SzArrayTypeAnalysisContext(type));
        var index=new LocalVariable("index",new Register(null,"X20"),app.SystemTypes.SystemInt32Type);
        var scaled=new LocalVariable("scaled",new Register(null,"TMP"));
        var address=new LocalVariable("address",new Register(null,"X8"));
        var value=new LocalVariable("value",new Register(null,"X0"),type);
        var memory=new MemoryOperand(address,addend:header);
        var access=store ? new Instruction(2,OpCode.Move,memory,value){NativeWriteSize=width}
            : new Instruction(2,OpCode.Move,value,memory){NativeReadSize=width};
        var method=new InjectedMethodAnalysisContext(type,"Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([
            new(0,OpCode.ShiftLeft,scaled,index,new Immediate(shift)),
            new(1,OpCode.Add,address,array,scaled),access,new(3,OpCode.Return)]);
        Assert.That(ArrayRecovery.RecoverSplitAccesses(method),Is.EqualTo(expected));
        var result=access.Operands[store?0:1] as ArrayAccess;
        Assert.That(result!=null,Is.EqualTo(expected));
        if(result!=null) { Assert.That(result.Array,Is.SameAs(array));Assert.That(result.Index,Is.SameAs(index)); }
    }
}
