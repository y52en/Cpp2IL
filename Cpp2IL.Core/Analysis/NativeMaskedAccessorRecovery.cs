using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Context-sensitive equivalent accessor, NOT a global native-address alias.
// Opt-in original full-FDE evidence plus the actual typed value receiver and
// exact boxed public getter are mandatory. Original method identity may differ.
public static class NativeMaskedAccessorRecovery
{
    public const string CountKey="NativeMaskedEquivalentAccessorCount";
    public sealed record Summary(int Count,WeakReference<ISILControlFlowGraph> Graph);
    private sealed record Leaf(byte[] Bytes,NativeMaskedScalarGetterShape.Read Read);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<ulong,Leaf>>> Cache=new();

    private static Dictionary<ulong,Leaf> Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_MASKED_FIELD_LOAD_PROOFS");
        if(string.IsNullOrEmpty(path))return new();
        var expected=Environment.GetEnvironmentVariable("CPP2IL_MASKED_FIELD_LOAD_PROOF_SHA256");
        if(!Path.IsPathFullyQualified(path) || expected?.Length!=64)throw new InvalidDataException("pinned masked field proof required");
        var raw=File.ReadAllBytes(path);
        if(!Convert.ToHexString(SHA256.HashData(raw)).Equals(expected,StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("masked proof changed");
        if(!CheckedUnboxRecovery.Supports(app))return new();
        using var doc=JsonDocument.Parse(raw);var root=doc.RootElement;
        if(root.GetProperty("schema").GetString()!="native-masked-field-load-leaves-v1"
            || !root.GetProperty("diagnostic_only").GetBoolean() || root.GetProperty("native_verified").GetBoolean()
            || root.GetProperty("adoption_allowed").GetBoolean()
            || root.GetProperty("binary_sha256").GetString()!="6bda601c39e4aaede3e4b09d79a0fcc0491606eb01e45fe5a89a1c2e3cc1af26"
            || root.GetProperty("metadata_sha256").GetString()!="78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e"
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !Convert.ToHexString(SHA256.HashData(metadata.ToArray())).Equals(root.GetProperty("metadata_sha256").GetString(),StringComparison.OrdinalIgnoreCase))
            throw new InvalidDataException("masked original profile differs");
        foreach(var pin in root.GetProperty("original_input_pins").EnumerateObject())
        {
            if(!Path.IsPathFullyQualified(pin.Name))throw new InvalidDataException("absolute masked proof input required");
            using var input=File.OpenRead(pin.Name);
            if(!Convert.ToHexString(SHA256.HashData(input)).Equals(pin.Value.GetString(),StringComparison.OrdinalIgnoreCase))throw new InvalidDataException("masked original input changed");
        }
        var rows=root.GetProperty("functions");var result=new Dictionary<ulong,Leaf>();
        if(rows.GetArrayLength()!=root.GetProperty("count").GetInt32())throw new InvalidDataException("masked proof count differs");
        foreach(var row in rows.EnumerateArray())
        {
            var address=Convert.ToUInt64(row.GetProperty("rva").GetString()!.Replace("0x",""),16);
            var bytes=Convert.FromHexString(row.GetProperty("bytes").GetString()!);
            if(address==0 || address%4!=0 || row.GetProperty("full_function_size").GetInt32()!=bytes.Length
                || NativeMaskedScalarGetterShape.Decode(bytes) is not {} read
                || read.Width!=row.GetProperty("width").GetInt32() || read.Offset!=row.GetProperty("offset").GetInt32()
                || read.Mask!=Convert.ToUInt64(row.GetProperty("mask").GetString()!.Replace("0x",""),16)
                || !Convert.ToHexString(SHA256.HashData(bytes)).Equals(row.GetProperty("sha256").GetString(),StringComparison.OrdinalIgnoreCase)
                || !app.Binary.TryMapVirtualAddressToRaw(address,out var offset) || offset<0 || offset>app.Binary.RawLength-bytes.Length
                || !app.Binary.GetRawBinaryContent().Slice((int)offset,bytes.Length).SequenceEqual(bytes)
                || !result.TryAdd(address,new(bytes,read)))throw new InvalidDataException("masked complete native bytes differ");
        }
        return result;
    }

    internal static TypeAnalysisContext? ReceiverType(IOperand operand)=>operand switch {
        AddressOf {Target:LocalVariable {Type.IsValueType:true} value}=>value.Type,
        LocalVariable {Type:ByRefTypeAnalysisContext reference}=>reference.ElementType,
        _=>null
    };
    private static int Width(TypeAnalysisContext? type)=>type?.FullName switch {
        "System.Int32" or "System.UInt32"=>4,"System.Int64" or "System.UInt64"=>8,_=>0
    };

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var leaves=Cache.GetValue(method.AppContext,a=>new Lazy<Dictionary<ulong,Leaf>>(()=>Load(a))).Value;
        if(leaves.Count==0)return 0;
        var count=0;
        foreach(var call in graph.Instructions.ToArray())
        {
            if(call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,
                Operands:[Immediate {Value:>0} address,LocalVariable result,var receiver,..]}
                || call.NativeDirectCallTarget!=address.UnsignedValue
                || !leaves.TryGetValue(address.UnsignedValue,out var unboxed)
                || call.Operands.Skip(3).Any(o=>o is not (LocalVariable or Immediate))
                || ReceiverType(receiver) is not {IsValueType:true} owner || owner.HasAnyGenericParameters()
                || owner.IsGenericInstance || Width(result.Type)!=unboxed.Read.Width)continue;
            var fields=owner.Fields.Where(f=>!f.IsStatic).ToArray();
            var field=fields.Where(f=>f.Offset==unboxed.Read.Offset && Width(f.FieldType)==unboxed.Read.Width).ToArray();
            if(field.Length!=1 || TypeSizes.UnboxedSize(owner,8)<unboxed.Read.Offset+unboxed.Read.Width
                || fields.Any(f=>!ReferenceEquals(f,field[0]) && f.Offset==field[0].Offset))continue;
            var candidates=owner.Methods.Where(m=>m.Name.StartsWith("get_",StringComparison.Ordinal)
                && !m.IsStatic && !m.IsVirtual && m.Visibility==System.Reflection.MethodAttributes.Public
                && m.Parameters.Count==0 && m.GenericParameters.Count==0
                && TrivialConstructorRecovery.SameType(m.ReturnType,result.Type)
                && owner.Properties.Count(p=>ReferenceEquals(p.Getter,m))==1
                && leaves.TryGetValue(m.UnderlyingPointer,out var boxed)
                && NativeMaskedReceiverPairShape.Equivalent(boxed.Bytes,unboxed.Bytes,16)).ToArray();
            if(candidates.Length!=1)continue;
            // No allocation, reordering or invented arguments. The exact same
            // pointer is consumed; only proven-unused register padding is dropped.
            call.SetOperands([candidates[0],result,receiver]);count++;
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
