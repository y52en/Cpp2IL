using System;

namespace Cpp2IL.Core.Analysis;

// Instruction effects only. The caller must separately authenticate a complete
// function extent, metadata field ownership and an equivalent managed accessor.
internal static class NativeMaskedScalarGetterShape
{
    internal sealed record Read(int Width,int Offset,ulong Mask);

    internal static Read? Decode(ReadOnlySpan<byte> bytes)
    {
        if(bytes.Length!=12 || BitConverter.ToUInt32(bytes.Slice(8,4))!=0xd65f03c0)return null;
        var load=BitConverter.ToUInt32(bytes.Slice(0,4));
        var and=BitConverter.ToUInt32(bytes.Slice(4,4));
        var width=(load&0xffc00000u) switch {0xf9400000u=>8,0xb9400000u=>4,_=>0};
        if(width==0 || ((load>>5)&31)!=0 || (load&31)==31
            || (and&0x7f800000u)!=0x12000000u || (and&31)!=0
            || ((and>>5)&31)!=(load&31) || (and>>31)!=(uint)(width==8?1:0))return null;
        var n=(int)((and>>22)&1);var s=(int)((and>>10)&63);var r=(int)((and>>16)&63);
        if(width==4 && n!=0)return null;
        var pattern=(n<<6)|(~s&63);var length=-1;
        for(var bit=6;bit>=0;bit--)if((pattern&(1<<bit))!=0){length=bit;break;}
        if(length<1 || length>(width==8?6:5))return null;
        var size=1<<length;var levels=size-1;var ones=s&levels;var rotate=r&levels;
        if(ones==levels)return null; // Reserved all-one logical immediate.
        var element=(1UL<<(ones+1))-1;
        var elementMask=size==64?ulong.MaxValue:(1UL<<size)-1;
        if(rotate!=0)element=((element>>rotate)|(element<<(size-rotate)))&elementMask;
        ulong mask=0;
        for(var bit=0;bit<width*8;bit+=size)mask|=element<<bit;
        return new(width,(int)((load>>10)&4095)*width,mask);
    }
}
