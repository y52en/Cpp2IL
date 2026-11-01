using System;
using System.Text;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeReceiverUnwindRangeTests
{
    private static void U16(byte[] raw,int at,ushort value)=>BitConverter.GetBytes(value).CopyTo(raw,at);
    private static void U32(byte[] raw,int at,uint value)=>BitConverter.GetBytes(value).CopyTo(raw,at);
    private static void U64(byte[] raw,int at,ulong value)=>BitConverter.GetBytes(value).CopyTo(raw,at);

    private static byte[] Fixture()
    {
        var raw=new byte[600];U32(raw,0,0x464c457f);raw[4]=2;raw[5]=1;
        U16(raw,18,183);U64(raw,40,64);U16(raw,58,64);U16(raw,60,4);U16(raw,62,1);
        var names="\0.shstrtab\0.eh_frame_hdr\0.eh_frame\0";
        Encoding.ASCII.GetBytes(names).CopyTo(raw,320);
        void Section(int index,string name,uint type,ulong flags,ulong address,ulong offset,ulong size)
        {
            var at=64+index*64;U32(raw,at,(uint)names.IndexOf(name+'\0',StringComparison.Ordinal));
            U32(raw,at+4,type);U64(raw,at+8,flags);U64(raw,at+16,address);
            U64(raw,at+24,offset);U64(raw,at+32,size);
        }
        Section(1,".shstrtab",3,0,0,320,(ulong)names.Length);
        Section(2,".eh_frame_hdr",1,2,0x1000,384,20);
        Section(3,".eh_frame",1,2,0x2000,448,44);
        U32(raw,384,0x3b031b01);U32(raw,388,0xffc);U32(raw,392,1);
        U32(raw,396,0x2000);U32(raw,400,0x1018);
        Convert.FromHexString("1400000000000000017a5200017c1e011b0c1f0000000000").CopyTo(raw,448);
        U32(raw,472,16);U32(raw,476,28);U32(raw,480,0xfe0);U32(raw,484,64);
        return raw;
    }

    [Test]
    public void HeaderAndFullFdeIndependentlyAgreeOnActualRange()
    {
        var result=NativeReceiverUnwindRanges.Parse(Fixture());
        Assert.That(result,Is.Not.Null);
        Assert.That(result!.Count,Is.EqualTo(1));
        Assert.That(result[0x3000],Is.EqualTo(64));
    }

    [TestCase("wrong-location")]
    [TestCase("wrong-cie")]
    [TestCase("unknown-cie-encoding")]
    [TestCase("wrong-frame-pointer")]
    [TestCase("short-fde")]
    [TestCase("overlong-fde")]
    [TestCase("zero-range")]
    [TestCase("duplicate-unsorted")]
    [TestCase("wrong-architecture")]
    [TestCase("unknown-header-encoding")]
    [TestCase("missing-allocated-section")]
    public void UnprovenPartialOrInconsistentRangeFailsClosed(string shape)
    {
        var raw=Fixture();
        switch(shape)
        {
            case "wrong-location":U32(raw,396,0x2004);break;
            case "wrong-cie":U32(raw,476,0);break;
            case "unknown-cie-encoding":raw[464]=0xff;break;
            case "wrong-frame-pointer":U32(raw,388,0);break;
            case "short-fde":U32(raw,472,8);break;
            case "overlong-fde":U32(raw,472,100);break;
            case "zero-range":U32(raw,484,0);break;
            case "duplicate-unsorted":U64(raw,192+32,28);U32(raw,392,2);U32(raw,404,0x2000);U32(raw,408,0x1018);break;
            case "wrong-architecture":U16(raw,18,62);break;
            case "unknown-header-encoding":raw[387]=0;break;
            case "missing-allocated-section":U64(raw,256+8,0);break;
        }
        Assert.That(NativeReceiverUnwindRanges.Parse(raw),Is.Null,shape);
    }

    [Test]
    public void TruncatedFileOrDuplicateSectionIsRejected()
    {
        var raw=Fixture();
        Assert.That(NativeReceiverUnwindRanges.Parse(raw.AsSpan(0,480)),Is.Null);
        Array.Copy(raw,192,raw,64,64);
        Assert.That(NativeReceiverUnwindRanges.Parse(raw),Is.Null);
    }
}
