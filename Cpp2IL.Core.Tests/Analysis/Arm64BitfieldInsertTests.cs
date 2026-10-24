using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64BitfieldInsertTests
{
    private static Arm64Instruction Native(bool wide,bool insert,int lsb,int count,int destination=9,int source=8)
    {
        var bits=wide?64:32;var immr=insert?(bits-lsb)%bits:lsb;
        var imms=insert?count-1:lsb+count-1;
        var word=(wide?0xb3400000u:0x33000000u)|(uint)immr<<16|(uint)imms<<10|(uint)source<<5|(uint)destination;
        return Disassembler.Disassemble(BitConverter.GetBytes(word),0x1ccf24c,new(true,true,false)).Single();
    }

    private static ulong Execute(List<Instruction> instructions,ulong old,ulong source,int destination=9)
    {
        var registers=new Dictionary<string,ulong>{{"X"+destination,old}};
        registers["X8"]=source;
        ulong Read(IOperand value)=>value switch{Register r=>registers[r.Name],Immediate i=>i.UnsignedValue,_=>throw new Exception()};
        foreach(var instruction in instructions)
        {
            var operands=instruction.Operands;var result=instruction.OpCode switch {
                OpCode.NumericConvert=>((Cpp2IL.Core.Model.Contexts.TypeAnalysisContext)operands[1]).FullName=="System.UInt32"
                    ?(uint)Read(operands[3]):Read(operands[3]),
                OpCode.And=>Read(operands[1])&Read(operands[2]),
                OpCode.Or=>Read(operands[1])|Read(operands[2]),
                OpCode.ShiftLeft=>Read(operands[1])<<(int)Read(operands[2]),
                OpCode.ShiftRightUnsigned=>Read(operands[1])>>(int)Read(operands[2]),_=>throw new Exception()};
            registers[((Register)operands[0]).Name]=result;
        }
        return registers["X"+destination];
    }

    [TestCase(false,false)]
    [TestCase(false,true)]
    [TestCase(true,false)]
    [TestCase(true,true)]
    public void EveryBitfieldRangeMatchesIndependentBitByBitReference(bool wide,bool insert)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;var bits=wide?64:32;
        foreach(var lsb in Enumerable.Range(1,bits-1))
        foreach(var count in Enumerable.Range(1,bits-lsb))
        {
            var native=Native(wide,insert,lsb,count);
            Assert.That(native.Mnemonic,Is.EqualTo(insert?Arm64Mnemonic.BFI:Arm64Mnemonic.BFXIL));
            var lowered=Arm64BitfieldInsertRecovery.Lower(native,types)!;Assert.That(lowered,Is.Not.Null);
            foreach(var pair in new[]{(0UL,ulong.MaxValue),(ulong.MaxValue,0UL),
                (0x0123456789abcdefUL,0xfedcba9876543210UL)})
            {
                var expected=wide?pair.Item1:(uint)pair.Item1;
                for(var n=0;n<count;n++)
                {
                    var dst=insert?n+lsb:n;var src=insert?n:n+lsb;
                    expected=(expected&~(1UL<<dst))|((pair.Item2>>src&1UL)<<dst);
                }
                Assert.That(Execute(lowered,pair.Item1,pair.Item2),Is.EqualTo(expected),native.ToString());
            }
        }
    }

    [Test]
    public void RealShakeBfiRetainsBitZeroAndReplacesUpper31Bits()
    {
        var native=Disassembler.Disassemble(Convert.FromHexString("09791f33"),0x1ccf24c,new(true,true,false)).Single();
        var result=Arm64BitfieldInsertRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(Execute(result,1,0xfffffffe),Is.EqualTo(0xfffffffdu));
        Assert.That(Execute(result,ulong.MaxValue,0),Is.EqualTo(1UL));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AliasedSourceAndDestinationUseOriginalValueBeforeWriting(bool wide)
    {
        var native=Native(wide,true,1,wide?63:31,8,8);
        var lowered=Arm64BitfieldInsertRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        var value=0x80123456789abcdfUL;var expected=(value<<1)|(value&1);
        if(!wide)expected=(uint)expected;
        Assert.That(Execute(lowered,value,value,8),Is.EqualTo(expected));
    }

    [TestCase(0xd503201fu)]
    [TestCase(0x1e202800u)]
    public void OtherNativeInstructionsCannotAuthorizeBitfieldRecovery(uint word)
    {
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        Assert.That(Arm64BitfieldInsertRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes),Is.Null);
    }
}
