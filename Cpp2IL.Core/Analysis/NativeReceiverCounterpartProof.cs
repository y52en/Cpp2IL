using System;
using System.Collections.Generic;
using System.Linq;

namespace Cpp2IL.Core.Analysis;

// Complete-FDE proof. Only the explicit receiver-header displacement may
// differ. Every opcode, register, branch and absolute callee is retained.
// This proves native counterparts only, never a managed method identity.
internal static class NativeReceiverCounterpartProof
{
    internal readonly record struct Effect(int Kind,uint Word,long Value=0);

    internal static Effect[]? Normalize(ReadOnlySpan<byte> code,ulong start,int header,bool voidReturn)
    {
        if(header is not (0 or 16) || code.Length is <4 or >4096 || code.Length%4!=0
            || start%4!=0 || start>long.MaxValue-4096)return null;
        var words=new uint[code.Length/4];
        for(var i=0;i<words.Length;i++)words[i]=BitConverter.ToUInt32(code.Slice(i*4,4));
        var effects=new Dictionary<int,Effect>();
        var pending=new Queue<(int Index,uint Aliases)>();
        var visited=new HashSet<(int,uint)>();pending.Enqueue((0,1));var accesses=0;
        static uint Bit(int reg)=>reg==31?0:1u<<reg;
        static long Signed(uint value,int bits)=>(int)(value<<(32-bits))>>(32-bits);
        while(pending.Count!=0)
        {
            var (index,aliases)=pending.Dequeue();
            if(!visited.Add((index,aliases)))continue;
            if(visited.Count>4096 || index<0 || index>=words.Length)return null;
            var word=words[index];var after=aliases;var effect=new Effect(0,word);
            var rd=(int)(word&31);var rn=(int)(word>>5&31);var rm=(int)(word>>16&31);
            var next=new List<int>();var branchMask=0u;long displacement=0;var call=false;var unconditional=false;
            if((word&0x7c000000)==0x14000000)
            {
                branchMask=0x03ffffff;displacement=Signed(word&branchMask,26);
                call=(word&0x80000000)!=0;unconditional=!call;
            }
            else if((word&0xff000010)==0x54000000 || (word&0x7e000000)==0x34000000)
            {
                branchMask=0x00ffffe0;displacement=Signed((word&branchMask)>>5,19);
                if((word&0x7e000000)==0x34000000 && (aliases&Bit(rd))!=0)return null;
            }
            else if((word&0x7e000000)==0x36000000)
            {
                branchMask=0x0007ffe0;displacement=Signed((word&branchMask)>>5,14);
                if((aliases&Bit(rd))!=0)return null;
            }
            if(branchMask!=0)
            {
                var target=(long)start+index*4+displacement*4;
                var internalTarget=target>=(long)start && target<(long)start+code.Length;
                if(call && internalTarget || !internalTarget && (aliases&255)!=0)return null;
                effect=new(internalTarget?1:2,word&~branchMask,internalTarget?target-(long)start:target);
                if(!unconditional)next.Add(index+1);
                if(internalTarget)next.Add((int)(target-(long)start)/4);
                if(call)after&=~((1u<<19)-1);
            }
            else if(word==0xd65f03c0)
            {if(!voidReturn && (aliases&1)!=0)return null;}
            else
            {
                next.Add(index+1);
                var move64=(word&0xffe0ffe0)==0xaa0003e0;
                var move32=(word&0xffe0ffe0)==0x2a0003e0;
                if(move64 || move32)
                {
                    if(move32 && (aliases&Bit(rm))!=0 || move64 && rd==31 && (aliases&Bit(rm))!=0)return null;
                    after&=~Bit(rd);
                    if(move64 && (aliases&Bit(rm))!=0)after|=Bit(rd);
                }
                else if((word&0x3b000000)==0x39000000)
                {
                    var vector=(word&0x04000000)!=0;var size=(int)(word>>30);var opc=(int)(word>>22&3);
                    if(vector && (size is not (2 or 3) || opc>1) || !vector && size==3 && opc>1)return null;
                    var load=opc!=0;var width=1<<size;
                    if(!load && !vector && (aliases&Bit(rd))!=0)return null;
                    if((aliases&Bit(rn))!=0)
                    {
                        var offset=(long)(word>>10&4095)*width-header;
                        if(offset<0)return null;
                        effect=new(3,word&~(4095u<<10),offset);accesses++;
                    }
                    if(load && !vector)after&=~Bit(rd);
                }
                else if((word&0x3a000000)==0x28000000)
                {
                    var vector=(word&0x04000000)!=0;var size=(int)(word>>30);var mode=(int)(word>>23&3);
                    var load=(word&0x00400000)!=0;var second=(int)(word>>10&31);
                    if(mode==0 || !vector && size==3 || !vector && size==1 && !load)return null;
                    var width=vector?4<<size:size==2?8:4;
                    if(!load && !vector && (aliases&(Bit(rd)|Bit(second)))!=0)return null;
                    if((aliases&Bit(rn))!=0)
                    {
                        if(mode!=2)return null;
                        var offset=Signed(word>>15&127,7)*width-header;
                        if(offset<0)return null;
                        effect=new(3,word&~(127u<<15),offset);accesses++;
                    }
                    if(load && !vector)after&=~(Bit(rd)|Bit(second));
                    if(mode is 1 or 3)after&=~Bit(rn);
                }
                else if((word&0x3b200000)==0x38000000)
                {
                    // Unscaled/pre/post-index storage is allowed only for
                    // non-receiver locations, retaining the complete word.
                    var vector=(word&0x04000000)!=0;var opc=(int)(word>>22&3);var mode=(int)(word>>10&3);
                    if((aliases&Bit(rn))!=0 || opc==0 && !vector && (aliases&Bit(rd))!=0)return null;
                    if(opc!=0 && !vector)after&=~Bit(rd);
                    if(mode is 1 or 3)after&=~Bit(rn);
                }
                else if((word&0x1f000000)==0x11000000)
                {if((aliases&Bit(rn))!=0)return null;after&=~Bit(rd);}
                else if((word&0x1f800000)==0x12800000)
                {if((word>>29&3)==3 && (aliases&Bit(rd))!=0)return null;after&=~Bit(rd);}
                else if((word&0x1f800000) is 0x13000000 or 0x13800000)
                {
                    if((aliases&Bit(rn))!=0 || (word&0x1f800000)==0x13800000 && (aliases&Bit(rm))!=0
                        || (word>>29&3)==1 && (aliases&Bit(rd))!=0)return null;
                    after&=~Bit(rd);
                }
                else if((word&0x1f000000) is 0x0a000000 or 0x0b000000 or 0x1a000000 or 0x1b000000)
                {
                    var read=Bit(rn)|Bit(rm);
                    if((word&0x1f000000)==0x1b000000)read|=Bit((int)(word>>10&31));
                    if((aliases&read)!=0)return null;after&=~Bit(rd);
                }
                else if(word!=0xd503201f)return null;
            }
            if(effects.TryGetValue(index,out var prior) && prior!=effect)return null;
            effects[index]=effect;
            foreach(var successor in next)pending.Enqueue((successor,after));
        }
        return effects.Count==words.Length && accesses>0?Enumerable.Range(0,words.Length).Select(i=>effects[i]).ToArray():null;
    }

    internal static bool Equivalent(ReadOnlySpan<byte> boxed,ulong a,ReadOnlySpan<byte> unboxed,ulong b,bool voidReturn)
        => Normalize(boxed,a,16,voidReturn)is {} left && Normalize(unboxed,b,0,voidReturn)is {} right
            && left.SequenceEqual(right);
}
