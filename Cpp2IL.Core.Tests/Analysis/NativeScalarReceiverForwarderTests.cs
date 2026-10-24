using System;
using System.Linq;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeScalarReceiverForwarderTests
{
    private static byte[] Body(ulong address,bool boxed,int width,bool floating=false)
    {
        uint load=floating?(width==4?0xbd401008u:0xfd400808u):(width==4?0xb9401013u:0xf9400813u);
        if(!boxed)load-=(uint)(16/width<<10);
        uint Branch(uint op,long target,int index)=>op|((uint)((target-(long)address-index*4)/4)&0x3ffffff);
        uint[] words=[floating?0xfc1e0fe8u:0xf81e0ff3u,0xa9017bfd,0x910043fd,load,
            0xaa1f03e0,Branch(0x94000000,0x3000,5),0xa9417bfd,0xaa0003e2,
            0x2a1303e0,0xaa1f03e1,0xaa1f03e3,0xf84207f3,Branch(0x14000000,0x4000,12)];
        return words.SelectMany(BitConverter.GetBytes).ToArray();
    }

    [TestCase(4,false)]
    [TestCase(8,false)]
    [TestCase(4,true)]
    [TestCase(8,true)]
    public void EntireFunctionWithRebasedCallsAndOnlyReceiverOffsetChangedMatches(int width,bool floating)
        =>Assert.That(NativeScalarReceiverForwarders.Equivalent(Body(0x1000,true,width,floating),0x1000,
            Body(0x2000,false,width,floating),0x2000,width),Is.True);

    [Test]
    public void NegativeCallAndTailDisplacementsAreSignExtendedBeforeRebasing()
        =>Assert.That(NativeScalarReceiverForwarders.Equivalent(Body(0x8000,true,4),0x8000,
            Body(0x9000,false,4),0x9000,4),Is.True);

    [TestCase("truncated")]
    [TestCase("width")]
    [TestCase("wrong-width")]
    [TestCase("receiver")]
    [TestCase("receiver-offset")]
    [TestCase("call-target")]
    [TestCase("tail-target")]
    [TestCase("same-relative-call-bits")]
    [TestCase("literal-pool")]
    [TestCase("adrp")]
    [TestCase("conditional")]
    [TestCase("indirect")]
    [TestCase("early-return")]
    [TestCase("early-tail")]
    [TestCase("missing-tail")]
    [TestCase("other-change")]
    [TestCase("unrelated-prologue")]
    [TestCase("unaligned")]
    public void IncompleteOrUnsupportedNativeContractsFailClosed(string shape)
    {
        var a=Body(0x1000,true,4);var b=Body(0x2000,false,4);var width=4;ulong address=0x2000;
        void Set(byte[] bytes,int index,uint word)=>BitConverter.GetBytes(word).CopyTo(bytes,index*4);
        if(shape=="truncated")b=b[..^1];
        if(shape=="width")width=0;
        if(shape=="wrong-width")width=8;
        if(shape=="receiver"){Set(a,3,0xb9401033);Set(b,3,0xb9400033);}
        if(shape=="receiver-offset")Set(a,3,0xb9400813);
        if(shape=="call-target")Set(b,5,BitConverter.ToUInt32(b,20)+1);
        if(shape=="tail-target")Set(b,12,BitConverter.ToUInt32(b,48)+1);
        if(shape=="same-relative-call-bits")Set(b,5,BitConverter.ToUInt32(a,20));
        var both=shape switch {"literal-pool"=>0x18000053u,"adrp"=>0x90000013u,
            "conditional"=>0x54000040u,"indirect"=>0xd63f0000u,"early-return"=>0xd65f03c0u,
            "early-tail"=>0x14000001u,_=>0u};
        if(both!=0){Set(a,6,both);Set(b,6,both);}
        if(shape=="missing-tail"){Set(a,12,0xd503201f);Set(b,12,0xd503201f);}
        if(shape=="other-change")Set(b,8,0x2a1403e0);
        if(shape=="unrelated-prologue"){Set(a,0,0xaa0003f3);Set(b,0,0xaa0003f3);}
        if(shape=="unaligned")address++;
        Assert.That(NativeScalarReceiverForwarders.Equivalent(a,0x1000,b,address,width),Is.False);
    }
}
