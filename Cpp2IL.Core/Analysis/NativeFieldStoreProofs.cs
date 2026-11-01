using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Re-decode the entire pinned original FDE, never trust supplied effect rows.
internal static class NativeFieldStoreProofs
{
    internal sealed record Entry(byte[] Bytes,NativeFieldLoadProofs.Read[] Stores);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<ulong,Entry>>> Cache=new();
    internal static IReadOnlyDictionary<ulong,Entry> For(ApplicationAnalysisContext app)
        =>Cache.GetValue(app,a=>new Lazy<Dictionary<ulong,Entry>>(()=>Load(a))).Value;

    private static Dictionary<ulong,Entry> Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_DIRECT_FIELD_STORE_PROOFS");
        var expected=Environment.GetEnvironmentVariable("CPP2IL_DIRECT_FIELD_STORE_PROOF_SHA256");
        if(string.IsNullOrEmpty(path))return new();
        if(app.UnityVersion.Major!=2018 || app.UnityVersion.Minor!=4 || !CheckedUnboxRecovery.Supports(app))return new();
        if(!Path.IsPathFullyQualified(path) || expected?.Length!=64)throw new InvalidDataException("pinned direct-store proof required");
        var raw=File.ReadAllBytes(path);
        if(!Convert.ToHexString(SHA256.HashData(raw)).Equals(expected,StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("direct-store proof changed");
        using var document=JsonDocument.Parse(raw);var root=document.RootElement;
        if(root.GetProperty("schema").GetString()!="native-direct-field-store-leaves-v1"
            || !root.GetProperty("diagnostic_only").GetBoolean() || root.GetProperty("native_verified").GetBoolean()
            || root.GetProperty("adoption_allowed").GetBoolean()
            || root.GetProperty("binary_sha256").GetString()!="6bda601c39e4aaede3e4b09d79a0fcc0491606eb01e45fe5a89a1c2e3cc1af26"
            || root.GetProperty("metadata_sha256").GetString()!="78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e"
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(root.GetProperty("metadata_sha256").GetString(),StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("direct-store original profile differs");
        foreach(var pin in root.GetProperty("original_input_pins").EnumerateObject())
        {
            if(!Path.IsPathFullyQualified(pin.Name))throw new InvalidDataException("absolute original store pin required");
            using var stream=File.OpenRead(pin.Name);
            if(!Convert.ToHexString(SHA256.HashData(stream)).Equals(pin.Value.GetString(),StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("direct-store original input changed");
        }
        var result=new Dictionary<ulong,Entry>();var functions=root.GetProperty("functions");
        if(functions.GetArrayLength()!=root.GetProperty("count").GetInt32())throw new InvalidDataException("direct-store extent count differs");
        foreach(var row in functions.EnumerateArray())
        {
            var address=Convert.ToUInt64(row.GetProperty("rva").GetString()!.Replace("0x",""),16);
            var bytes=Convert.FromHexString(row.GetProperty("bytes").GetString()!);
            if(address==0 || address%4!=0 || row.GetProperty("full_function_size").GetInt32()!=bytes.Length
                || Decode(bytes) is not {} stores
                || !Convert.ToHexString(SHA256.HashData(bytes)).Equals(row.GetProperty("sha256").GetString(),StringComparison.OrdinalIgnoreCase)
                || !app.Binary.TryMapVirtualAddressToRaw(address,out var offset)
                || offset<0 || offset>app.Binary.RawLength-bytes.Length
                || !app.Binary.GetRawBinaryContent().Slice((int)offset,bytes.Length).SequenceEqual(bytes)
                || !result.TryAdd(address,new(bytes,stores)))throw new InvalidDataException("direct-store complete original bytes differ");
        }
        return result;
    }

    internal static NativeFieldLoadProofs.Read[]? Decode(ReadOnlySpan<byte> bytes)
    {
        if(bytes.Length is not (8 or 12 or 16 or 20) || BitConverter.ToUInt32(bytes[^4..])!=0xd65f03c0)return null;
        var stores=new List<NativeFieldLoadProofs.Read>();var occupied=new HashSet<long>();
        for(var index=0;index<bytes.Length/4-1;index++)
        {
            var word=BitConverter.ToUInt32(bytes.Slice(index*4,4));if(((word>>5)&31)!=0)return null;
            var opcode=word&0xffc00000u;
            var scalar=opcode switch {0x39000000u=>("gpr",1),0x79000000u=>("gpr",2),
                0xb9000000u=>("gpr",4),0xf9000000u=>("gpr",8),0xbd000000u=>("fp",4),0xfd000000u=>("fp",8),_=>("",0)};
            var pair=opcode switch {0x29000000u=>("gpr",4),0xa9000000u=>("gpr",8),
                0x2d000000u=>("fp",4),0x6d000000u=>("fp",8),_=>("",0)};
            if(scalar.Item2!=0)stores.Add(new(scalar.Item1,(int)(word&31),scalar.Item2,((word>>10)&4095)*scalar.Item2,index));
            else if(pair.Item2!=0)
            {
                var immediate=(int)((word>>15)&127);if((immediate&64)!=0)immediate-=128;
                stores.Add(new(pair.Item1,(int)(word&31),pair.Item2,(long)immediate*pair.Item2,index));
                stores.Add(new(pair.Item1,(int)((word>>10)&31),pair.Item2,(long)(immediate+1)*pair.Item2,index));
            }
            else return null;
        }
        if(stores.Count is <1 or >4 || stores.Select(s=>s.Kind).Distinct().Count()!=1
            || stores.Select(s=>(s.Kind,s.Register)).Distinct().Count()!=stores.Count)return null;
        foreach(var store in stores)
        {
            if(store.Offset<16 || (store.Kind=="gpr"?store.Register is not (1 or 2):store.Register>3))return null;
            for(var address=store.Offset;address<store.Offset+store.Width;address++)if(!occupied.Add(address))return null;
        }
        return stores.ToArray();
    }
}
