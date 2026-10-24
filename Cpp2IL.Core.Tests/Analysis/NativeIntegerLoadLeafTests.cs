using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeIntegerLoadLeafTests
{
    [TestCase("zero",true)]
    [TestCase("unrelated",true)]
    [TestCase("overwritten-zero",true)]
    [TestCase("missing",false)]
    [TestCase("nonzero",false)]
    [TestCase("memory",false)]
    [TestCase("alias",false)]
    [TestCase("version",false)]
    [TestCase("clobber",false)]
    [TestCase("call",false)]
    [TestCase("branch",false)]
    [TestCase("redefined",false)]
    [TestCase("late-zero",false)]
    [TestCase("not-call",false)]
    [TestCase("negative-index",false)]
    [TestCase("past-end",false)]
    public void OnlyAnExplicitUnclobberedNullMethodInfoMayPreemptTypedAccessorRecovery(string shape,bool expected)
    {
        var x1=new Register(null,"X1");
        var zero=new Instruction(1,OpCode.Move,x1,new Immediate(0));
        var call=new Instruction(9,OpCode.CallVoid,new Immediate(0x1234));
        var block=new Block{Instructions=[zero,call]};
        if(shape=="missing")block.Instructions.Remove(zero);
        if(shape=="nonzero")zero.SetOperand(1,new Immediate(0x9876));
        if(shape=="memory")zero.SetOperand(1,new MemoryOperand(new Register(null,"X8")));
        if(shape=="alias")zero.SetOperand(1,new Register(null,"X2"));
        if(shape=="version")zero.SetOperand(0,new Register(null,"X1",0));
        if(shape=="unrelated")block.Instructions.Insert(1,new(2,OpCode.Move,new Register(null,"X2"),new Immediate(3)));
        if(shape=="overwritten-zero")block.Instructions.Insert(0,new(0,OpCode.Move,x1,new Immediate(3)));
        if(shape=="clobber")block.Instructions.Insert(1,new Instruction(2,OpCode.Nop){ImplicitDefinition=x1});
        if(shape=="call")block.Instructions.Insert(1,new(2,OpCode.CallVoid,new Immediate(0x9876)));
        if(shape=="branch")block.Instructions.Insert(1,new(2,OpCode.Jump,new Immediate(0x9999)));
        if(shape=="redefined")block.Instructions.Insert(1,new(2,OpCode.Move,x1,new Immediate(3)));
        if(shape=="late-zero"){block.Instructions.Remove(zero);block.Instructions.Add(zero);}
        if(shape=="not-call")call.OpCode=OpCode.Nop;
        var index=shape=="negative-index"?-1:shape=="past-end"?block.Instructions.Count:block.Instructions.IndexOf(call);
        var original=block.Instructions.ToArray();
        Assert.That(NativeIntegerLoadLeafExpansion.HasNullMethodInfo(block,index),Is.EqualTo(expected));
        Assert.That(block.Instructions,Is.EqualTo(original));
    }

    [TestCase("000040b9c0035fd6",4,0)]
    [TestCase("000040f9c0035fd6",8,0)]
    [TestCase("000840b9c0035fd6",4,8)]
    [TestCase("000840f9c0035fd6",8,16)]
    [TestCase("00fc7fb9c0035fd6",4,16380)]
    [TestCase("00fc7ff9c0035fd6",8,32760)]
    public void ExactGprLoadReturnKeepsWidthAndOffset(string code,int width,long offset)
    {
        var result=NativeIntegerLoadLeafExpansion.Decode(Convert.FromHexString(code));
        Assert.That(result,Is.Not.Null);Assert.That(result!.Value.Width,Is.EqualTo(width));
        Assert.That(result.Value.Offset,Is.EqualTo(offset));
    }

    [TestCase("")]
    [TestCase("000040b9")]
    [TestCase("000040b9c0035fd7")]
    [TestCase("200040b9c0035fd6")]
    [TestCase("010040b9c0035fd6")]
    [TestCase("000040bdc0035fd6")]
    [TestCase("00004039c0035fd6")]
    [TestCase("00004079c0035fd6")]
    [TestCase("000080b9c0035fd6")]
    [TestCase("000000b9c0035fd6")]
    [TestCase("00044029c0035fd6")]
    [TestCase("00000014c0035fd6")]
    [TestCase("000040b9c0035fd61f2003d5")]
    public void OtherBasesDestinationsExtensionsWidthsStoresBranchesAndExtraBytesAreRejected(string code)
        =>Assert.That(NativeIntegerLoadLeafExpansion.Decode(Convert.FromHexString(code)),Is.Null);

    [TestCase("word",true)]
    [TestCase("doubleword",true)]
    [TestCase("void",true)]
    [TestCase("width",false)]
    [TestCase("negative",false)]
    [TestCase("unaligned",false)]
    [TestCase("overflow",false)]
    [TestCase("abi",false)]
    [TestCase("version",false)]
    [TestCase("clobber",false)]
    [TestCase("target",false)]
    [TestCase("return",false)]
    [TestCase("virtual",false)]
    public void ExpansionWritesActualGprReturnOnlyWhenRawAbiIsIntact(string shape,bool expected)
    {
        var operands=new System.Collections.Generic.List<IOperand>{new Immediate(0x1234)};
        if(shape!="void")operands.Add(new Register(null,shape=="return"?"X1":"X0"));
        operands.AddRange(Enumerable.Range(0,16).Select(n=>(IOperand)new Register(null,n<8?"X"+n:"V"+(n-8))));
        if(shape=="abi")operands[^1]=new Register(null,"V6");
        if(shape=="version")operands[^1]=new Register(null,"V7",0);
        var call=new Instruction(5,shape=="void"?OpCode.CallVoid:OpCode.Call,operands);
        if(shape=="clobber")call.ImplicitDefinition=new Register(null,"X0");
        if(shape=="target")call.NativeDirectCallTarget=0x9999;
        if(shape=="virtual")call.NativeVirtualDispatch=true;
        var block=new Block{ID=2,Instructions=[call]};var before=call.Operands.ToArray();var serial=100;
        var width=shape=="doubleword"?8:shape=="width"?2:4;
        var offset=shape=="negative"?-4:shape=="unaligned"?3:shape=="overflow"?65536:8;
        Assert.That(NativeIntegerLoadLeafExpansion.Rewrite(block,0,width,offset,ref serial),Is.EqualTo(expected));
        if(!expected)
        {Assert.That(block.Instructions,Is.EqualTo(new[]{call}));Assert.That(call.Operands,Is.EqualTo(before));Assert.That(serial,Is.EqualTo(100));return;}
        Assert.That(block.Instructions.Count,Is.EqualTo(2));Assert.That(block.Instructions[1],Is.SameAs(call));
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(serial,Is.EqualTo(101));
        var load=block.Instructions[0];Assert.That(load.Operands[0],Is.EqualTo(new Register(null,"X0")));
        var memory=(MemoryOperand)load.Operands[1];Assert.That(memory.Base,Is.EqualTo(new Register(null,"X0")));
        Assert.That(memory.Addend,Is.EqualTo(offset));Assert.That(load.NativeReadSize,Is.EqualTo(width));
        Assert.That(load.NativeWriteSize,Is.Zero);Assert.That(call.NativeDirectCallTarget,Is.Zero);
    }
}
