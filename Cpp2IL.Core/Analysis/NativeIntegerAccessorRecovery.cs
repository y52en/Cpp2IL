using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Opt-in original complete-FDE counterparts, never a native-address alias.
// SDK bounded arithmetic diagnostics are NOT an acceptance certificate.
public static class NativeIntegerAccessorRecovery
{
    public const string CountKey="NativeIntegerEquivalentAccessorCount";
    public sealed record Summary(int Count,WeakReference<ISILControlFlowGraph> Graph);
    private sealed record Contract(ulong Unboxed,ulong Boxed,byte[] BoxedBytes,byte[] UnboxedBytes,
        string Owner,string Getter,string ReturnType,string FieldName,string FieldType,int FieldOffset,int LoadWidth);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Contract[]>> Cache=new();
    private static ulong Address(JsonElement row,string key)=>Convert.ToUInt64(row.GetProperty(key).GetString()!.Replace("0x",""),16);
    private static string Text(JsonElement row,string key)=>row.GetProperty(key).GetString()??throw new InvalidDataException("missing integer getter identity");
    private static int Width(string name)=>name switch {"System.Int32" or "System.UInt32"=>4,"System.Int64" or "System.UInt64"=>8,_=>0};

    private static bool LoadShape(byte[] raw,int offset,int width)
    {
        if(raw.Length<8 || raw.Length>128 || raw.Length%4!=0 || offset<0 || width is not (4 or 8))return false;
        var first=BitConverter.ToUInt32(raw,0);
        return (first&0xffc003e0u)==(width==8?0xf9400000u:0xb9400000u)
            && ((first>>10)&0xfff)*width==offset && BitConverter.ToUInt32(raw,raw.Length-4)==0xd65f03c0u;
    }

    private static Contract[] Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_INTEGER_ACCESSOR_PROOFS");
        if(string.IsNullOrEmpty(path))return [];
        var expected=Environment.GetEnvironmentVariable("CPP2IL_INTEGER_ACCESSOR_PROOF_SHA256");
        if(!Path.IsPathFullyQualified(path) || expected?.Length!=64)throw new InvalidDataException("pinned integer accessor proof required");
        var raw=File.ReadAllBytes(path);
        if(!Convert.ToHexString(SHA256.HashData(raw)).Equals(expected,StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("integer accessor proof changed");
        if(!CheckedUnboxRecovery.Supports(app))return [];
        using var doc=JsonDocument.Parse(raw);var root=doc.RootElement;
        if(Text(root,"schema")!="native-integer-accessor-counterparts-v1" || !root.GetProperty("diagnostic_only").GetBoolean()
            || root.GetProperty("native_verified").GetBoolean() || root.GetProperty("adoption_allowed").GetBoolean()
            || root.GetProperty("formal_sdk_equivalence_proved").GetBoolean()
            || Text(root,"binary_sha256")!="6bda601c39e4aaede3e4b09d79a0fcc0491606eb01e45fe5a89a1c2e3cc1af26"
            || Text(root,"metadata_sha256")!="78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e"
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(Text(root,"metadata_sha256"),StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("integer accessor original profile differs");
        foreach(var pin in root.GetProperty("input_pins").EnumerateObject())
        {
            if(!Path.IsPathFullyQualified(pin.Name))throw new InvalidDataException("absolute integer proof input required");
            using var input=File.OpenRead(pin.Name);
            if(!Convert.ToHexString(SHA256.HashData(input)).Equals(pin.Value.GetString(),StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("integer proof input changed");
        }
        bool Matches(ulong address,byte[] bytes)=>address!=0 && address%4==0
            && app.Binary.TryMapVirtualAddressToRaw(address,out var offset) && offset>=0 && offset<=app.Binary.RawLength-bytes.Length
            && app.Binary.GetRawBinaryContent().Slice((int)offset,bytes.Length).SequenceEqual(bytes);
        var rows=root.GetProperty("functions");var contracts=new List<Contract>();
        if(rows.GetArrayLength()!=root.GetProperty("count").GetInt32())throw new InvalidDataException("integer proof count differs");
        foreach(var row in rows.EnumerateArray())
        {
            var c=new Contract(Address(row,"unboxed_rva"),Address(row,"boxed_rva"),Convert.FromHexString(Text(row,"boxed_bytes")),
                Convert.FromHexString(Text(row,"unboxed_bytes")),Text(row,"owner"),Text(row,"getter"),Text(row,"return_type"),
                Text(row,"field_name"),Text(row,"field_type"),row.GetProperty("field_offset").GetInt32(),row.GetProperty("load_width").GetInt32());
            if(!row.GetProperty("only_receiver_input").GetBoolean() || Width(c.ReturnType)==0 || Width(c.FieldType)!=c.LoadWidth
                || !LoadShape(c.BoxedBytes,c.FieldOffset+16,c.LoadWidth) || !LoadShape(c.UnboxedBytes,c.FieldOffset,c.LoadWidth)
                || c.BoxedBytes.Length!=c.UnboxedBytes.Length
                || (BitConverter.ToUInt32(c.BoxedBytes,0)&~0x003ffc00u)!=(BitConverter.ToUInt32(c.UnboxedBytes,0)&~0x003ffc00u)
                || !c.BoxedBytes.AsSpan(4).SequenceEqual(c.UnboxedBytes.AsSpan(4))
                || !Matches(c.Boxed,c.BoxedBytes) || !Matches(c.Unboxed,c.UnboxedBytes))
                throw new InvalidDataException("complete integer getter native bytes differ");
            contracts.Add(c);
        }
        return contracts.ToArray();
    }

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var contracts=Cache.GetValue(method.AppContext,a=>new Lazy<Contract[]>(()=>Load(a))).Value;
        if(contracts.Length==0)return 0;
        var count=0;
        foreach(var call in graph.Instructions.ToArray())
        {
            if(call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,
                Operands:[Immediate {Value:>0} address,LocalVariable result,var receiver,..]}
                || call.NativeDirectCallTarget!=address.UnsignedValue
                || call.Operands.Skip(3).Any(o=>o is not (LocalVariable or Immediate))
                || NativeMaskedAccessorRecovery.ReceiverType(receiver) is not {IsValueType:true} owner
                || owner.HasAnyGenericParameters() || owner.IsGenericInstance)continue;
            var matches=new List<MethodAnalysisContext>();
            foreach(var c in contracts.Where(c=>c.Unboxed==address.UnsignedValue && c.Owner==owner.FullName))
            {
                if(result.Type!=null && result.Type.FullName!=c.ReturnType)continue;
                var fields=owner.Fields.Where(f=>!f.IsStatic).ToArray();
                var field=fields.Where(f=>f.Offset==c.FieldOffset && f.Name==c.FieldName && f.FieldType?.FullName==c.FieldType).ToArray();
                if(field.Length!=1 || fields.Any(f=>!ReferenceEquals(f,field[0]) && f.Offset==c.FieldOffset)
                    || TypeSizes.UnboxedSize(owner,8)<c.FieldOffset+c.LoadWidth)continue;
                matches.AddRange(owner.Methods.Where(m=>m.Name==c.Getter && m.UnderlyingPointer==c.Boxed
                    && !m.IsStatic && !m.IsVirtual && m.Visibility==System.Reflection.MethodAttributes.Public
                    && m.Parameters.Count==0 && m.GenericParameters.Count==0 && m.ReturnType.FullName==c.ReturnType
                    && owner.Properties.Count(p=>ReferenceEquals(p.Getter,m))==1));
            }
            var getters=matches.Distinct().ToArray();
            if(getters.Length!=1)continue;
            // The original typed metadata getter determines the missing return
            // type. Existing incompatible caller types are rejected above.
            result.Type??=getters[0].ReturnType;
            call.SetOperands([getters[0],result,receiver]);count++;
        }
        if(count>0)
        {
            var previous=method.GetExtraData<Summary>(CountKey);
            var before=previous!=null && previous.Graph.TryGetTarget(out var old) && ReferenceEquals(old,graph)?previous.Count:0;
            method.PutExtraData(CountKey,new Summary(before+count,new(graph)));
        }
        return count;
    }
}
