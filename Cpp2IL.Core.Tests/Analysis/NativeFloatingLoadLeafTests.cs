using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeFloatingLoadLeafTests
{
    [TestCase("000840bdc0035fd6",4,8)]
    [TestCase("000c40bdc0035fd6",4,12)]
    [TestCase("000440fdc0035fd6",8,8)]
    [TestCase("000040bdc0035fd6",4,0)]
    [TestCase("00fc7fbdc0035fd6",4,16380)]
    public void CompleteScalarFpLoadReturnKeepsNativeWidthAndOffset(string code,int width,long offset)
    {
        var result=NativeFloatingLoadLeafExpansion.Decode(Convert.FromHexString(code));
        Assert.That(result,Is.Not.Null);Assert.That(result!.Value.Width,Is.EqualTo(width));
        Assert.That(result.Value.Offset,Is.EqualTo(offset));
    }

    [TestCase("000840bd")]
    [TestCase("000840bdc0035fd7")]
    [TestCase("200840bdc0035fd6")]
    [TestCase("010840bdc0035fd6")]
    [TestCase("000840b9c0035fd6")]
    [TestCase("000800bdc0035fd6")]
    [TestCase("0004402dc0035fd6")]
    [TestCase("00000014c0035fd6")]
    public void NonFpNonreceiverPartialBranchAndOtherReturnRecipesAreRejected(string code)
        => Assert.That(NativeFloatingLoadLeafExpansion.Decode(Convert.FromHexString(code)),Is.Null);

    [TestCase("single",true)]
    [TestCase("double",true)]
    [TestCase("void",true)]
    [TestCase("width",false)]
    [TestCase("negative",false)]
    [TestCase("unaligned",false)]
    [TestCase("overflow",false)]
    [TestCase("abi",false)]
    [TestCase("clobber",false)]
    [TestCase("target",false)]
    [TestCase("return",false)]
    public void ExpansionWritesTheActualFpReturnAndNeverOverwritesTheReceiver(string shape,bool expected)
    {
        var operands=new System.Collections.Generic.List<IOperand>{new Immediate(0x1234)};
        if(shape!="void")operands.Add(new Register(null,shape=="return"?"X1":"X0"));
        operands.AddRange(Enumerable.Range(0,16).Select(n=>(IOperand)new Register(null,n<8?"X"+n:"V"+(n-8))));
        if(shape=="abi")operands[^1]=new Register(null,"V6");
        var call=new Instruction(5,shape=="void"?OpCode.CallVoid:OpCode.Call,operands);
        if(shape=="clobber")call.ImplicitDefinition=new Register(null,"X0");
        if(shape=="target")call.NativeDirectCallTarget=0x9999;
        var block=new Block{ID=2,Instructions=[call]};var before=call.Operands.ToArray();var serial=100;
        var width=shape=="double"?8:shape=="width"?2:4;
        var offset=shape=="negative"?-4:shape=="unaligned"?3:shape=="overflow"?65536:8;
        Assert.That(NativeFloatingLoadLeafExpansion.Rewrite(block,0,width,offset,ref serial),Is.EqualTo(expected));
        if(!expected)
        {Assert.That(block.Instructions,Is.EqualTo(new[]{call}));Assert.That(call.Operands,Is.EqualTo(before));Assert.That(serial,Is.EqualTo(100));return;}
        Assert.That(block.Instructions.Count,Is.EqualTo(2));Assert.That(block.Instructions[1],Is.SameAs(call));
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(serial,Is.EqualTo(101));
        var load=block.Instructions[0];Assert.That(load.Operands[0],Is.EqualTo(new Register(null,"V0")));
        var memory=(MemoryOperand)load.Operands[1];Assert.That(memory.Base,Is.EqualTo(new Register(null,"X0")));
        Assert.That(memory.Addend,Is.EqualTo(offset));Assert.That(load.NativeReadSize,Is.EqualTo(width));
        Assert.That(load.NativeWriteSize,Is.Zero);
    }
}
