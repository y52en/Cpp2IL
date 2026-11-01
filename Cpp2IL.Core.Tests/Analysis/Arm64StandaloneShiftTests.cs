using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64StandaloneShiftTests
{
    static Arm64Instruction Native(bool wide,string operation,int amount)
    {
        var bits=wide?64:32;
        uint word=operation=="asr"?(wide?0x93400000u:0x13000000u):(wide?0xd3400000u:0x53000000u);
        var immr=operation=="lsl"?bits-amount:amount;
        var imms=operation=="lsl"?bits-1-amount:bits-1;
        word|=(uint)immr<<16|(uint)imms<<10|22u<<5|10u;
        return Disassembler.Disassemble(BitConverter.GetBytes(word),0x1d167d0,new(true,true,false)).Single();
    }

    [TestCase(false,"lsr")]
    [TestCase(true,"lsr")]
    [TestCase(false,"asr")]
    [TestCase(true,"asr")]
    [TestCase(false,"lsl")]
    [TestCase(true,"lsl")]
    public void EveryImmediateWidthAndKindMatchesNativeBitVectors(bool wide,string operation)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        foreach(var amount in new[]{1,wide?63:31})
        {
            var lowered=Arm64ShiftedLogicalRecovery.LowerStandalone(Native(wide,operation,amount),types);
            Assert.That(lowered,Is.Not.Null);
            foreach(var input in new[]{0UL,1UL,0x80000000UL,uint.MaxValue,0x8000000000000000UL,ulong.MaxValue})
            {
                var value=wide?input:(uint)input;
                var expected=operation switch
                {
                    "lsr"=>value>>amount,"lsl"=>value<<amount,
                    _=>wide?unchecked((ulong)((long)value>>amount)):unchecked((uint)((int)value>>amount)),
                };
                if(!wide)expected=(uint)expected;
                Assert.That(Arm64ShiftedLogicalTests.Execute(lowered!,0,input),Is.EqualTo(expected));
            }
        }
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RegisterShiftCountsUseNativeModuloBitWidth(bool wide)
    {
        var word=(wide?0x9ac02400u:0x1ac02400u)|(19u<<16)|(22u<<5)|10u;
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        var lowered=Arm64ShiftedLogicalRecovery.LowerStandalone(native,TestGameLoader.LoadSimple2019Game().SystemTypes);
        Assert.That(lowered,Is.Not.Null,native.ToString());
        foreach(var count in new[]{0UL,1UL,31UL,32UL,63UL,64UL,ulong.MaxValue})
        {
            var expected=wide?ulong.MaxValue>>(int)(count&63):uint.MaxValue>>(int)(count&31);
            Assert.That(Arm64ShiftedLogicalTests.Execute(lowered!,count,ulong.MaxValue),Is.EqualTo(expected));
        }
    }

    [TestCase(4,0x40000000L)]
    [TestCase(8,0x4000000000000000L)]
    public void UnsignedConstantFoldingUsesTheExactNativeWidth(int width,long expected)
    {
        var instruction=new Instruction(0,OpCode.ShiftRightUnsigned,new Register(null,"result"),
            new Immediate(width==4?unchecked((long)0x80000000):long.MinValue),new Immediate(1)){NativeArithmeticSize=width};
        Assert.That(ConstantFolder.Run(new ISILControlFlowGraph([instruction,new(1,OpCode.Return)])),Is.True);
        Assert.That(instruction.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(((Immediate)instruction.Operands[1]).Value,Is.EqualTo(expected));
    }

    [Test]
    public void UnknownWidthDoesNotAuthorizeUnsignedConstantFolding()
    {
        var instruction=new Instruction(0,OpCode.ShiftRightUnsigned,new Register(null,"result"),new Immediate(-1),new Immediate(1));
        Assert.That(ConstantFolder.Run(new ISILControlFlowGraph([instruction,new(1,OpCode.Return)])),Is.False);
        Assert.That(instruction.SourcesAndConstants.Count,Is.EqualTo(2));
    }
}
