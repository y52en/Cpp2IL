using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Original FDE extents/bytes only. Managed ownership and EVERY concrete
// instantiation must still be independently established by the consumer.
internal static class NativeFieldLoadProofs
{
    internal sealed record Read(string Kind,int Register,int Width,long Offset,int Instruction);
    internal sealed record Entry(byte[] Bytes,Read[] Reads);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<ulong,Entry>>> Cache=new();

    internal static IReadOnlyDictionary<ulong,Entry> For(ApplicationAnalysisContext app)
        =>Cache.GetValue(app,a=>new Lazy<Dictionary<ulong,Entry>>(()=>Load(a))).Value;

    private static Dictionary<ulong,Entry> Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_DIRECT_FIELD_LOAD_PROOFS");
        var expected=Environment.GetEnvironmentVariable("CPP2IL_DIRECT_FIELD_LOAD_PROOF_SHA256");
        if(string.IsNullOrEmpty(path))return new();
        if(app.UnityVersion.Major!=2018 || app.UnityVersion.Minor!=4 || !CheckedUnboxRecovery.Supports(app))return new();
        if(!Path.IsPathFullyQualified(path) || expected?.Length!=64)throw new InvalidDataException("pinned direct-field proof required");
        var raw=File.ReadAllBytes(path);
        if(!Convert.ToHexString(SHA256.HashData(raw)).Equals(expected,StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("direct-field proof changed");
        using var document=JsonDocument.Parse(raw);var root=document.RootElement;
        if(root.GetProperty("schema").GetString()!="native-direct-field-load-leaves-v1"
            || !root.GetProperty("diagnostic_only").GetBoolean() || root.GetProperty("native_verified").GetBoolean()
            || root.GetProperty("binary_sha256").GetString()!="6bda601c39e4aaede3e4b09d79a0fcc0491606eb01e45fe5a89a1c2e3cc1af26"
            || root.GetProperty("metadata_sha256").GetString()!="78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e"
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(root.GetProperty("metadata_sha256").GetString(),StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("direct-field original profile differs");
        foreach(var pin in root.GetProperty("original_input_pins").EnumerateObject())
        {
            if(!Path.IsPathFullyQualified(pin.Name))throw new InvalidDataException("absolute original proof pin required");
            using var stream=File.OpenRead(pin.Name);
            if(!Convert.ToHexString(SHA256.HashData(stream)).Equals(pin.Value.GetString(),StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("direct-field original input changed");
        }
        var result=new Dictionary<ulong,Entry>();var functions=root.GetProperty("functions");
        if(functions.GetArrayLength()!=root.GetProperty("count").GetInt32())throw new InvalidDataException("direct-field extent count differs");
        foreach(var row in functions.EnumerateArray())
        {
            var address=Convert.ToUInt64(row.GetProperty("rva").GetString()!.Replace("0x",""),16);
            var bytes=Convert.FromHexString(row.GetProperty("bytes").GetString()!);
            if(address==0 || address%4!=0 || row.GetProperty("full_function_size").GetInt32()!=bytes.Length
                || Decode(bytes) is not {} reads
                || !Convert.ToHexString(SHA256.HashData(bytes)).Equals(row.GetProperty("sha256").GetString(),StringComparison.OrdinalIgnoreCase)
                || !app.Binary.TryMapVirtualAddressToRaw(address,out var offset)
                || offset<0 || offset>app.Binary.RawLength-bytes.Length
                || !app.Binary.GetRawBinaryContent().Slice((int)offset,bytes.Length).SequenceEqual(bytes)
                || !result.TryAdd(address,new(bytes,reads)))throw new InvalidDataException("direct-field complete original bytes differ");
        }
        return result;
    }

    internal static Read[]? Decode(ReadOnlySpan<byte> bytes)
    {
        if(bytes.Length is not (8 or 12 or 16 or 20) || BitConverter.ToUInt32(bytes[^4..])!=0xd65f03c0)return null;
        var result=new List<Read>();var count=bytes.Length/4-1;
        for(var i=0;i<count;i++)
        {
            var word=BitConverter.ToUInt32(bytes.Slice(i*4,4));if(((word>>5)&31)!=0)return null;
            var opcode=word&0xffc00000u;
            var scalar=opcode switch {
                0x39400000u or 0x39c00000u or 0x39800000u=>("gpr",1),
                0x79400000u or 0x79c00000u or 0x79800000u=>("gpr",2),
                0xb9400000u or 0xb9800000u=>("gpr",4),0xf9400000u=>("gpr",8),
                0xbd400000u=>("fp",4),0xfd400000u=>("fp",8),_=>("",0)};
            var pair=opcode switch {0x29400000u=>("gpr",4),0xa9400000u=>("gpr",8),
                0x2d400000u=>("fp",4),0x6d400000u=>("fp",8),_=>("",0)};
            if(scalar.Item2!=0)result.Add(new(scalar.Item1,(int)(word&31),scalar.Item2,((word>>10)&4095)*scalar.Item2,i));
            else if(pair.Item2!=0)
            {
                var immediate=(int)((word>>15)&127);if((immediate&64)!=0)immediate-=128;
                result.Add(new(pair.Item1,(int)(word&31),pair.Item2,(long)immediate*pair.Item2,i));
                result.Add(new(pair.Item1,(int)((word>>10)&31),pair.Item2,(long)(immediate+1)*pair.Item2,i));
            }
            else return null;
        }
        if(result.Count is <1 or >4 || result.Select(r=>r.Kind).Distinct().Count()!=1
            || result.Select(r=>(r.Kind,r.Register)).Distinct().Count()!=result.Count
            || result.Any(r=>r.Offset<16 || r.Register>(r.Kind=="fp"?3:1)
                || r.Kind=="gpr" && r.Register==0 && r.Instruction<count-1))return null;
        return result.ToArray();
    }
}
