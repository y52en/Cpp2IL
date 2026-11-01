using System;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Tests.Analysis;

public class ReadOnlyScalarRecoveryTests
{
    [TestCase(".rodata",2L,0x1000UL,4,true)]
    [TestCase(".rodata.cst8",2L,0x1008UL,8,true)]
    [TestCase(".rodata",3L,0x1000UL,4,false)]
    [TestCase(".rodata",6L,0x1000UL,4,false)]
    [TestCase(".rodata",0L,0x1000UL,4,false)]
    [TestCase(".data.rel.ro",2L,0x1000UL,4,false)]
    [TestCase(".text",2L,0x1000UL,4,false)]
    [TestCase(".rodata",2L,0x1000UL,16,false)]
    [TestCase(".rodata",2L,0x100CUL,8,false)]
    [TestCase(".rodata",2L,0xFFFUL,4,false)]
    public void ScalarRegionRequiresExactReadonlyAllocatedFileBytes(string name,long flags,ulong address,int width,bool expected)
    {
        var section=new ElfSectionHeaderEntry {Name=name,Flags=(ElfSectionHeaderFlags)flags,
            Type=ElfSectionEntryType.SHT_PROGBITS,VirtualAddress=0x1000,Size=16};
        Assert.That(ElfFile.IsReadOnlyScalarSection(section,address,width),Is.EqualTo(expected));
        section.Type=ElfSectionEntryType.SHT_NOBITS;
        Assert.That(ElfFile.IsReadOnlyScalarSection(section,address,width),Is.False);
    }

    [TestCase("System.Single",4,0xBF800000UL)]
    [TestCase("System.Single",4,0x80000000UL)]
    [TestCase("System.Single",4,1UL)]
    [TestCase("System.Double",8,0x8000000000000000UL)]
    public void TypedFloatReadsPreserveBitsNotNumericCast(string type,int width,ulong bits)
    {
        var value=ReadOnlyScalarRecovery.Decode(type,width,bits);
        var recovered=value is FloatLiteral f ? (ulong)(uint)BitConverter.SingleToInt32Bits(f.Value)
            : (ulong)BitConverter.DoubleToInt64Bits(((DoubleLiteral)value!).Value);
        Assert.That(recovered,Is.EqualTo(bits));
    }

    [TestCase("System.Int32",4,0xFFFFFFFFUL,-1L)]
    [TestCase("System.UInt32",4,0xFFFFFFFFUL,4294967295L)]
    [TestCase("System.Int64",8,0xFFFFFFFFFFFFFFFFUL,-1L)]
    public void ScalarIntegerReadsKeepSignedness(string type,int width,ulong bits,long expected)
        => Assert.That(((Immediate)ReadOnlyScalarRecovery.Decode(type,width,bits)!).Value,Is.EqualTo(expected));

    [TestCase("System.Single",8)]
    [TestCase("System.Double",4)]
    [TestCase("System.IntPtr",8)]
    [TestCase("System.Object",8)]
    [TestCase("System.Byte",1)]
    public void MismatchedWidthsAndPointerTypesAreNotGuessed(string type,int width)
        => Assert.That(ReadOnlyScalarRecovery.Decode(type,width,0),Is.Null);
}
