using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete original FDE counterparts, independently pinned by the ELF audit.
// Never enters MethodsByAddress and never binds a managed method by its name.
internal static class NativeRegisteredReceiverLeafProofs
{
    internal readonly record struct Effect(uint Word,int Offset,bool Load);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<(ulong,ulong),bool>>> Cache=new();

    internal static Effect[]? Normalize(ReadOnlySpan<byte> code,int header)
    {
        if(code.Length is <8 or >20 || code.Length%4!=0 || header is not (0 or 16))return null;
        var result=new List<Effect>();var clobbered=false;var loads=0;
        for(var offset=0;offset<code.Length;offset+=4)
        {
            var word=BitConverter.ToUInt32(code.Slice(offset,4));
            if(offset==code.Length-4)
            {if(word!=0xd65f03c0)return null;result.Add(new(word,0,false));continue;}
            var opcode=word&0xffc00000u;
            var width=opcode switch {
                0x39400000 or 0x39c00000 or 0x39800000=>1,
                0x79400000 or 0x79c00000 or 0x79800000=>2,
                0xb9400000 or 0xb9800000 or 0xbd400000=>4,
                0xf9400000 or 0xfd400000=>8,_=>0};
            var pairWidth=opcode switch {0xa9400000 or 0x6d400000=>8,0x29400000 or 0x2d400000=>4,_=>0};
            if(width!=0 || pairWidth!=0)
            {
                if(clobbered || (word>>5&31)!=0)return null;
                int displacement;uint normalized;bool floating;
                if(width!=0)
                {
                    displacement=(int)(word>>10&4095)*width;normalized=word&~(4095u<<10);
                    floating=opcode is 0xbd400000 or 0xfd400000;
                    if(!floating && (word&31)==0)clobbered=true;
                }
                else
                {
                    var immediate=(int)(word>>15&127);
                    displacement=(immediate>=64?immediate-128:immediate)*pairWidth;
                    normalized=word&~(127u<<15);floating=opcode is 0x6d400000 or 0x2d400000;
                    if(!floating && ((word&31)==0 || (word>>10&31)==0))clobbered=true;
                }
                if(displacement<header)return null;
                result.Add(new(normalized,displacement-header,true));loads++;continue;
            }
            // Only the exact ORR register alias used for MOV is admitted.
            // A live raw receiver may not escape into a different register.
            if((word&0xffe0ffe0u) is not (0xaa0003e0u or 0x2a0003e0u)
                || !clobbered && (word>>16&31)==0)return null;
            if((word&31)==0)clobbered=true;
            result.Add(new(word,0,false));
        }
        return loads!=0?result.ToArray():null;
    }

    internal static bool Equivalent(ReadOnlySpan<byte> boxed,ReadOnlySpan<byte> unboxed)
        => Normalize(boxed,16)is {} a && Normalize(unboxed,0)is {} b && a.SequenceEqual(b);

    internal static bool CompleteNoop(ReadOnlySpan<byte> boxed,ReadOnlySpan<byte> unboxed)
        => boxed.Length==4 && unboxed.Length==4 && BitConverter.ToUInt32(boxed)==0xd65f03c0
            && boxed.SequenceEqual(unboxed);

    internal static bool VoidNoopMethod(MethodAnalysisContext method)
        => method is ConcreteGenericMethodAnalysisContext {MethodRef:not null,IsStatic:false,IsVoid:true,
            DeclaringType:{IsValueType:true}} && method.Parameters.Count==0;

    private static Dictionary<(ulong,ulong),bool> Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_REGISTERED_RECEIVER_LEAF_PROOFS");
        if(string.IsNullOrEmpty(path))return [];
        var pin=Environment.GetEnvironmentVariable("CPP2IL_REGISTERED_RECEIVER_LEAF_PROOF_SHA256");
        if(!Path.IsPathFullyQualified(path)||pin?.Length!=64)throw new InvalidDataException("pinned receiver leaf evidence required");
        var raw=File.ReadAllBytes(path);
        if(!Convert.ToHexString(SHA256.HashData(raw)).Equals(pin,StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("receiver leaf evidence changed");
        if(!CheckedUnboxRecovery.Supports(app))return [];
        using var document=JsonDocument.Parse(raw);var root=document.RootElement;
        var schema=root.GetProperty("schema").GetString();
        if(schema is not ("registered-receiver-leaf-counterparts-v1" or "registered-receiver-leaf-counterparts-v2")
            || !root.GetProperty("diagnostic_only").GetBoolean() || root.GetProperty("native_verified").GetBoolean()
            || root.GetProperty("adoption_allowed").GetBoolean() || root.GetProperty("target_executed").GetBoolean()
            || !root.GetProperty("input_pins_unchanged").GetBoolean() || root.GetProperty("scope_count").GetInt32()!=14845
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(
                "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("receiver evidence original profile differs");
        foreach(var input in root.GetProperty("input_pins").EnumerateObject())
        {
            if(!Path.IsPathFullyQualified(input.Name))throw new InvalidDataException("absolute receiver evidence input required");
            using var stream=File.OpenRead(input.Name);
            if(!Convert.ToHexString(SHA256.HashData(stream)).Equals(input.Value.GetString(),StringComparison.OrdinalIgnoreCase))
                throw new InvalidDataException("receiver proof provenance changed");
        }
        bool Actual(ulong entry,byte[] bytes)=>entry!=0 && entry%4==0
            && app.Binary.TryMapVirtualAddressToRaw(entry,out var rawOffset) && rawOffset>=0
            && rawOffset<=app.Binary.RawLength-bytes.Length
            && app.Binary.GetRawBinaryContent().Slice((int)rawOffset,bytes.Length).SequenceEqual(bytes);
        var result=new Dictionary<(ulong,ulong),bool>();
        foreach(var row in root.GetProperty("counterparts").EnumerateArray())
        {
            var boxed=Convert.ToUInt64(row.GetProperty("boxed_rva").GetString()!.Replace("0x",""),16);
            var unboxed=Convert.ToUInt64(row.GetProperty("unboxed_rva").GetString()!.Replace("0x",""),16);
            var a=Convert.FromHexString(row.GetProperty("boxed_bytes").GetString()!);
            var b=Convert.FromHexString(row.GetProperty("unboxed_bytes").GetString()!);
            var noop=row.TryGetProperty("effect_kind",out var kind)&&kind.GetString()=="void_noop";
            if(boxed==unboxed || a.Length!=row.GetProperty("boxed_fde_length").GetInt32()
                || b.Length!=row.GetProperty("unboxed_fde_length").GetInt32()
                || !Actual(boxed,a) || !Actual(unboxed,b)
                || (noop ? schema!="registered-receiver-leaf-counterparts-v2"
                    || !row.GetProperty("required_return_void").GetBoolean()
                    || row.GetProperty("required_parameter_count").GetInt32()!=0 || !CompleteNoop(a,b)
                    : !Equivalent(a,b)) || !result.TryAdd((boxed,unboxed),noop))
                throw new InvalidDataException("unproved receiver leaf counterpart");
        }
        return result;
    }

    internal static bool Matches(MethodAnalysisContext method,ulong entry)
    {
        if(entry==0 || method is not ConcreteGenericMethodAnalysisContext {MethodRef:not null,IsStatic:false,
            DeclaringType:{IsValueType:true}} || method.UnderlyingPointer==0)return false;
        return Cache.GetValue(method.AppContext,app=>new Lazy<Dictionary<(ulong,ulong),bool>>(()=>Load(app))).Value
            .TryGetValue((method.UnderlyingPointer,entry),out var noop) && (!noop || VoidNoopMethod(method));
    }
}
