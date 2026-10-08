using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Disarm;

namespace Cpp2IL.Core.Tests;

public class UnboxingAdjustorTests
{
    [Test]
    public void ExactArm64BoxHeaderAdjustmentAndTailBranchResolve()
    {
        byte[] bytes=[0,0x40,0,0x91,2,0,0,0x14]; // ADD X0,X0,#16; B +8
        var body=Disassembler.Disassemble(bytes,0x1000,new(true,true,false)).ToList();
        Assert.That(NewArmV8InstructionSet.RecognizeUnboxingAdjustor(body),Is.EqualTo(0x100CUL));
    }

    [TestCase(0,0x20)] // wrong header size
    [TestCase(0,0x41)] // different destination
    [TestCase(3,0x11)] // W0, not X0
    [TestCase(7,0x94)] // BL, not tail branch
    public void UnsupportedAdjustmentIsNotAnAlias(int index,int value)
    {
        byte[] bytes=[0,0x40,0,0x91,2,0,0,0x14];
        if(index==0 && value==0x20) bytes[1]=0x20;
        else if(index==0 && value==0x41) bytes[0]=1;
        else bytes[index]=(byte)value;
        var body=Disassembler.Disassemble(bytes,0x1000,new(true,true,false)).ToList();
        Assert.That(NewArmV8InstructionSet.RecognizeUnboxingAdjustor(body),Is.Zero);
    }

    [Test]
    public void AdditionalInstructionsCannotBeSilentlyDiscarded()
    {
        byte[] bytes=[0,0x40,0,0x91,2,0,0,0x14,0xC0,3,0x5F,0xD6];
        var body=Disassembler.Disassemble(bytes,0x1000,new(true,true,false)).ToList();
        Assert.That(NewArmV8InstructionSet.RecognizeUnboxingAdjustor(body),Is.Zero);
    }
}
