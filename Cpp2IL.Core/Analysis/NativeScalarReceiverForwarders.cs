using System;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Complete Ghidra1178/1180, whole-FDE audit1189 and metadata evidence1191:
// c08f00e0d4383a9bba9f9f357d4567cbf0d8fe32f322a2efbd053fe8f4e11ea9.
// Distinct from the leaf catalog: preserve every call/tail and its absolute
// target. Only this exact original loaded image AND metadata can use these rows.
internal static class NativeScalarReceiverForwarders
{
    private sealed record Contract(string Owner,ulong Boxed,ulong Unboxed,int Length,uint Token,int Width,string Parameters="");
    private static readonly Contract[] Contracts=[
        new("System.Int32",0xa6914c,0x11bc030,52,0x60009ec,4),
        new("System.Int32",0xa69180,0x11bc064,56,0x60009ed,4,"System.String"),
        new("System.Int32",0xa691b8,0x11bc09c,56,0x60009ee,4,"System.IFormatProvider"),
        new("System.Int32",0xa691f0,0x11ac470,60,0x60009ef,4,"System.String|System.IFormatProvider"),
        new("System.Int64",0xa692f0,0x11bcae8,52,0x6000a0b,8),
        new("System.Int64",0xa69324,0x11bcb1c,56,0x6000a0c,8,"System.IFormatProvider"),
        new("System.Int64",0xa6935c,0x11bcb54,56,0x6000a0d,8,"System.String"),
        new("System.Int64",0xa69394,0x11bcb8c,60,0x6000a0e,8,"System.String|System.IFormatProvider"),
        new("System.UInt32",0xa6ef74,0x143b5dc,52,0x6000df4,4),
        new("System.UInt32",0xa6efa8,0x143b610,56,0x6000df5,4,"System.IFormatProvider"),
        new("System.UInt32",0xa6efe0,0x143b648,60,0x6000df6,4,"System.String|System.IFormatProvider"),
        new("System.UInt64",0xa6f0e0,0x143c058,52,0x6000e11,8),
        new("System.UInt64",0xa6f114,0x143c08c,56,0x6000e12,8,"System.IFormatProvider"),
        new("System.UInt64",0xa6f14c,0x143c0c4,56,0x6000e13,8,"System.String"),
        new("System.UInt64",0xa6f184,0x143c0fc,60,0x6000e14,8,"System.String|System.IFormatProvider"),
        new("System.Double",0xc126c8,0x1b74ec0,52,0x600084d,8),
        new("System.Double",0xc126fc,0x1b74ef4,56,0x600084e,8,"System.IFormatProvider"),
        new("System.Double",0xc12734,0x1b74f2c,68,0x600084f,8,"System.String|System.IFormatProvider"),
        new("System.Single",0xc1b980,0x1d9e0f4,52,0x6000b93,4),
        new("System.Single",0xc1b9b4,0x1d9e128,56,0x6000b94,4,"System.IFormatProvider"),
        new("System.Single",0xc1b9ec,0x1d9e160,64,0x6000b95,4,"System.String"),
        new("System.Single",0xc1ba2c,0x1d9e1a0,68,0x6000b96,4,"System.String|System.IFormatProvider"),
    ];
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<bool>> MetadataIdentities=new();

    internal static int ProvenLength(MethodAnalysisContext method,ulong target)
    {
        var row=Contracts.FirstOrDefault(r=>r.Boxed==method.UnderlyingPointer && r.Unboxed==target);
        return row!=null && Target(method)==target?row.Length:0;
    }

    internal static ulong Target(MethodAnalysisContext method)
    {
        var row=Contracts.FirstOrDefault(r=>r.Boxed==method.UnderlyingPointer);
        if(row==null || method.IsStatic || method.Name!="ToString" || method.Definition?.token!=row.Token
            || method.DeclaringType is not {IsValueType:true} owner || owner.FullName!=row.Owner
            || owner.DeclaringAssembly.Name!="mscorlib" || owner.HasAnyGenericParameters()
            || method.GenericParameters.Count!=0 || method.ReturnType.FullName!="System.String"
            || string.Join("|",method.Parameters.Select(p=>p.ParameterType.FullName))!=row.Parameters)return 0;
        var fields=owner.Fields.Where(f=>!f.IsStatic).ToArray();
        if(fields.Length!=1 || fields[0].Name!="m_value" || fields[0].Offset!=0
            || fields[0].FieldType.FullName!=row.Owner || TypeSizes.UnboxedSize(owner,8)!=row.Width
            || !CheckedUnboxRecovery.Supports(method.AppContext)
            || !MetadataIdentities.GetValue(method.AppContext,app=>new Lazy<bool>(()=>
                app.Metadata.BaseStream is MemoryStream stream && string.Equals(
                    Convert.ToHexString(SHA256.HashData(stream.ToArray())),
                    "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",StringComparison.OrdinalIgnoreCase))).Value)return 0;
        var binary=method.AppContext.Binary;
        if(!binary.TryMapVirtualAddressToRaw(row.Boxed,out var a) || !binary.TryMapVirtualAddressToRaw(row.Unboxed,out var b)
            || a<0 || b<0 || a>binary.RawLength-row.Length || b>binary.RawLength-row.Length)return 0;
        var bytes=binary.GetRawBinaryContent();
        return Equivalent(bytes.Slice((int)a,row.Length),row.Boxed,bytes.Slice((int)b,row.Length),row.Unboxed,row.Width)
            ?row.Unboxed:0;
    }

    internal static bool Equivalent(ReadOnlySpan<byte> boxed,ulong a,ReadOnlySpan<byte> unboxed,ulong b,int width)
    {
        if(boxed.Length!=unboxed.Length || boxed.Length is <20 or >256 || boxed.Length%4!=0 || width is not (4 or 8)
            || a%4!=0 || b%4!=0 || a==b)return false;
        uint Word(ReadOnlySpan<byte> bytes,int n)=>BitConverter.ToUInt32(bytes.Slice(n*4,4));
        var prelude=Word(boxed,0)==0xfc1e0fe8 && Word(boxed,1)==0xf90007f3?4:3;
        if(Word(boxed,0) is not (0xf81e0ff3 or 0xa9be4ff4 or 0xfc1e0fe8)
            || Word(boxed,prelude-2)!=0xa9017bfd || Word(boxed,prelude-1)!=0x910043fd)return false;
        var changed=0;var calls=0;var finished=false;
        for(var n=0;n<boxed.Length/4;n++)
        {
            var x=Word(boxed,n);var y=Word(unboxed,n);var last=n==boxed.Length/4-1;
            if((x&0x7c000000)==0x14000000)
            {
                if((y&0xfc000000)!=(x&0xfc000000) || (x&0x80000000)==0 && !last)return false;
                static long Target(uint word,ulong pc)=>(long)pc+((long)((int)(word<<6)>>6)<<2);
                if(Target(x,a+(ulong)n*4)!=Target(y,b+(ulong)n*4))return false;
                calls++;if((x&0x80000000)==0)finished=true;continue;
            }
            if(x==0xd65f03c0)
            {if(!last || y!=x)return false;finished=true;continue;}
            if((x&0x1f000000)==0x10000000 || (x&0x3b000000)==0x18000000
                || (x&0xff000010)==0x54000000 || (x&0x7e000000) is 0x34000000 or 0x36000000
                || (x&0xfe000000)==0xd6000000)return false;
            if(n==prelude)
            {
                var opcode=x&0xffc003e0;
                if(calls!=0 || (width==4?opcode is not (0xb9400000 or 0xbd400000):opcode is not (0xf9400000 or 0xfd400000))
                    || ((x>>10)&0xfff)!=(uint)(16/width) || y!=x-(uint)(16/width<<10))return false;
                changed++;continue;
            }
            if(x!=y)return false;
        }
        return changed==1 && calls>0 && finished;
    }
}
