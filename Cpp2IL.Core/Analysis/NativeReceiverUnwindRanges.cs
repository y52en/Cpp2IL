using System;
using System.Collections.Generic;
using System.Text;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Read the original ARM64 ELF unwind table independently of proposal lengths.
// Explicitly support only the observed ELF64-LE table/CIE encodings. Unknown,
// truncated, duplicate and disagreeing table/FDE records fail closed.
internal static class NativeReceiverUnwindRanges
{
    internal static Dictionary<ulong,int>? ForImage(ApplicationAnalysisContext app)=>Parse(app.Binary.GetRawBinaryContent());
    private readonly record struct Section(ulong Address,int Offset,int Size);
    private static ushort U16(ReadOnlySpan<byte> raw,int at)=>BitConverter.ToUInt16(raw.Slice(at,2));
    private static uint U32(ReadOnlySpan<byte> raw,int at)=>BitConverter.ToUInt32(raw.Slice(at,4));
    private static ulong U64(ReadOnlySpan<byte> raw,int at)=>BitConverter.ToUInt64(raw.Slice(at,8));
    private static int I32(ReadOnlySpan<byte> raw,int at)=>BitConverter.ToInt32(raw.Slice(at,4));
    private static bool Bounds(ulong at,ulong size,int length)=>at<=(ulong)length && size<=(ulong)length-at;

    private static bool SupportedCie(ReadOnlySpan<byte> raw,int at,int size)
    {
        if(size is not (24 or 32) || U32(raw,at+4)!=0 || raw[at+8]!=1)return false;
        if(size==24)
            return raw[at+9]==(byte)'z' && raw[at+10]==(byte)'R' && raw[at+11]==0
                && raw[at+12] is 1 or 4 && raw[at+13] is 0x7c or 0x78 && raw[at+14]==30
                && raw[at+15]==1 && raw[at+16]==0x1b;
        if(raw[at+9]!=(byte)'z' || raw[at+10]!=(byte)'P' || raw[at+11]!=(byte)'L'
            || raw[at+12]!=(byte)'R' || raw[at+13]!=0 || raw[at+14] is not (1 or 4)
            || raw[at+15] is not (0x7c or 0x78) || raw[at+16]!=30)return false;
        var personalitySize=raw[at+18]switch {0x9b=>4,0x9c=>8,_=>0};
        return personalitySize!=0 && raw[at+17]==personalitySize+3
            && raw[at+19+personalitySize] is 0x1b or 0x1c && raw[at+20+personalitySize]==0x1b;
    }

    internal static Dictionary<ulong,int>? Parse(ReadOnlySpan<byte> raw)
    {
        if(!BitConverter.IsLittleEndian || raw.Length<64 || U32(raw,0)!=0x464c457f
            || raw[4]!=2 || raw[5]!=1 || U16(raw,18)!=183 || U16(raw,58)!=64)return null;
        var table=U64(raw,40);var count=U16(raw,60);var stringsIndex=U16(raw,62);
        if(count<4 || stringsIndex>=count || !Bounds(table,(ulong)count*64,raw.Length))return null;
        var stringsHeader=(int)table+stringsIndex*64;
        var stringsOffset=U64(raw,stringsHeader+24);var stringsSize=U64(raw,stringsHeader+32);
        if(!Bounds(stringsOffset,stringsSize,raw.Length))return null;
        Section? header=null,frame=null;
        for(var index=0;index<count;index++)
        {
            var at=(int)table+index*64;var nameOffset=U32(raw,at);
            if(nameOffset>=stringsSize)return null;
            var remaining=raw.Slice((int)(stringsOffset+nameOffset),(int)(stringsSize-nameOffset));
            var end=remaining.IndexOf((byte)0);if(end<0)return null;
            var name=Encoding.ASCII.GetString(remaining.Slice(0,end).ToArray());
            if(name is not (".eh_frame_hdr" or ".eh_frame"))continue;
            var offset=U64(raw,at+24);var size=U64(raw,at+32);
            if(U32(raw,at+4)!=1 || (U64(raw,at+8)&3)!=2 || !Bounds(offset,size,raw.Length))return null;
            var section=new Section(U64(raw,at+16),(int)offset,(int)size);
            if(section.Address>long.MaxValue-(ulong)section.Size)return null;
            if(name==".eh_frame_hdr") {if(header!=null)return null;header=section;}
            else {if(frame!=null)return null;frame=section;}
        }
        if(header is not {} h || frame is not {} f || h.Size<12
            || U32(raw,h.Offset)!=0x3b031b01
            || (long)h.Address+4+I32(raw,h.Offset+4)!=(long)f.Address)return null;
        var entries=U32(raw,h.Offset+8);
        if(entries is 0 or >1000000 || 12UL+entries*8UL>(ulong)h.Size)return null;
        var result=new Dictionary<ulong,int>();var validatedCies=new HashSet<int>();ulong prior=0;
        for(var index=0u;index<entries;index++)
        {
            var at=h.Offset+12+(int)index*8;
            var initial=(long)h.Address+I32(raw,at);var fdeAddress=(long)h.Address+I32(raw,at+4);
            if(initial<=0 || index!=0 && (ulong)initial<=prior || fdeAddress<(long)f.Address
                || fdeAddress>(long)f.Address+f.Size-16)return null;
            var fde=f.Offset+(int)(fdeAddress-(long)f.Address);var recordLength=U32(raw,fde);
            if(recordLength<12 || recordLength>(ulong)(f.Offset+f.Size-fde-4))return null;
            var distance=U32(raw,fde+4);
            if(distance==0 || distance>(ulong)(fde+4-f.Offset))return null;
            var cie=fde+4-(int)distance;
            if(!validatedCies.Contains(cie))
            {
                if(cie>f.Offset+f.Size-8)return null;
                var length=U32(raw,cie);
                if(length>28 || length>(ulong)(f.Offset+f.Size-cie-4)
                    || !SupportedCie(raw,cie,(int)length+4))return null;
                validatedCies.Add(cie);
            }
            var start=fdeAddress+8+I32(raw,fde+8);var size=I32(raw,fde+12);
            if(start!=initial || size<=0 || initial>long.MaxValue-size)return null;
            if(!result.TryAdd((ulong)initial,size))return null;
            prior=(ulong)initial;
        }
        return result;
    }
}
