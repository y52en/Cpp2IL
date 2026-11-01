using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Original whole-FDE audit1589 and complete Ghidra1592: GetTogetherData is
// exactly LDR X0,[X0,#16];RET. Recover a proven PUBLIC nonvirtual API from its
// inlined native field effect, not from Get/Is naming conventions. The rebuilt
// caller must still pass compilation, exact native and global/replay gates.
public static class NativePublicFieldAccessorRecovery
{
    internal sealed record Contract(MethodAnalysisContext Method,int Width);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<FieldAnalysisContext,Contract>>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph==null || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        var catalog=Catalogs.GetValue(method.AppContext,a=>new Lazy<Dictionary<FieldAnalysisContext,Contract>>(()=>Build(a))).Value;
        return Recover(method,catalog);
    }

    private static Dictionary<FieldAnalysisContext,Contract> Build(ApplicationAnalysisContext app)
    {
        if(app.Metadata.BaseStream is not MemoryStream metadata || !Convert.ToHexString(SHA256.HashData(metadata.ToArray()))
            .Equals("78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",StringComparison.OrdinalIgnoreCase))return new();
        var candidates=new Dictionary<FieldAnalysisContext,List<Contract>>();var binary=app.Binary;
        foreach(var target in app.MethodsByAddress.Values.SelectMany(v=>v).Distinct())
        {
            if(target.DeclaringType is not {IsValueType:false} owner || target.IsStatic || target.IsVirtual
                || target.Visibility!=MethodAttributes.Public || target.Parameters.Count!=0 || target.IsVoid
                || target.GenericParameters.Count!=0 || owner.IsGenericInstance || owner.GenericParameters.Count!=0
                || target.Name.StartsWith(".",StringComparison.Ordinal)
                || owner.Properties.Any(p=>ReferenceEquals(p.Getter,target))
                || target.UnderlyingPointer==0 || target.UnderlyingPointer%4!=0
                || !binary.TryMapVirtualAddressToRaw(target.UnderlyingPointer,out var raw)
                || raw<0 || raw>binary.RawLength-8
                || app.GetAddressOfNextFunctionStart(target.UnderlyingPointer)!=target.UnderlyingPointer+8)continue;
            var code=binary.GetRawBinaryContent().Slice((int)raw,8);
            foreach(var field in owner.Fields)
            {
                if(!TryContract(target,field,code,out var width))continue;
                if(!candidates.TryGetValue(field,out var list))candidates[field]=list=[];
                list.Add(new(target,width));
            }
        }
        // Multiple public API identities stay unresolved rather than choosing
        // an arbitrary overload/name. The exact native field is the map key.
        return candidates.Where(p=>p.Value.Count==1).ToDictionary(p=>p.Key,p=>p.Value[0]);
    }

    internal static bool TryContract(MethodAnalysisContext target,FieldAnalysisContext field,ReadOnlySpan<byte> code,out int width)
    {
        width=0;
        if(code.Length!=8 || BitConverter.ToUInt32(code[4..])!=0xd65f03c0u
            || target.DeclaringType is not {IsValueType:false} owner || target.IsStatic || target.IsVirtual || target.IsVoid
            || target.Visibility!=MethodAttributes.Public || target.Parameters.Count!=0 || target.GenericParameters.Count!=0
            || owner.IsGenericInstance || owner.GenericParameters.Count!=0 || target.Name.StartsWith(".",StringComparison.Ordinal)
            || owner.Properties.Any(p=>ReferenceEquals(p.Getter,target))
            || !ReferenceEquals(field.DeclaringType,owner) || !owner.Fields.Contains(field) || field.IsStatic
            || (field.Attributes&FieldAttributes.Literal)!=0 || field.Offset<16
            || !TrivialConstructorRecovery.SameType(field.FieldType,target.ReturnType))return false;
        var returned=target.ReturnType;var scalar=returned.IsEnumType?returned.EnumUnderlyingType:returned;
        if(scalar==null)return false;
        var (encoding,bytes)=scalar.FullName switch {
            "System.Boolean" or "System.Byte"=>(0x39400000u,1),"System.SByte"=>(0x39c00000u,1),
            "System.Char" or "System.UInt16"=>(0x79400000u,2),"System.Int16"=>(0x79c00000u,2),
            "System.Int32" or "System.UInt32"=>(0xb9400000u,4),
            "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr"=>(0xf9400000u,8),
            "System.Single"=>(0xbd400000u,4),"System.Double"=>(0xfd400000u,8),_=>(0u,0)};
        if(!returned.IsValueType && !returned.HasAnyGenericParameters() && returned.Type is
            Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or Il2CppTypeEnum.IL2CPP_TYPE_STRING
                or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST)
        {encoding=0xf9400000u;bytes=8;}
        var word=BitConverter.ToUInt32(code[..4]);
        if(bytes==0 || (word&0xffc003ffu)!=encoding || ((word>>10)&4095)*bytes!=field.Offset)return false;
        width=bytes;return true;
    }

    private static bool Receiver(LocalVariable local,TypeAnalysisContext owner)
    {
        if(local.Type is not {IsValueType:false} type || type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            || type.Type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST))return false;
        var seen=new HashSet<TypeAnalysisContext>();
        for(var current=type;current!=null && seen.Add(current) && seen.Count<=32;current=current.BaseType)
            if(TrivialConstructorRecovery.SameType(current,owner))return true;
        return false;
    }

    internal static int Recover(MethodAnalysisContext method,IReadOnlyDictionary<FieldAnalysisContext,Contract> catalog)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var count=0;
        foreach(var block in graph.Blocks)
        foreach(var instruction in block.Instructions)
        {
            if(instruction is not {OpCode:OpCode.Move,NativeWriteSize:0,
                Operands:[LocalVariable result,FieldReference {Parent:null} field]}
                || !catalog.TryGetValue(field.Field,out var contract) || field.Offset!=field.Field.Offset
                || instruction.NativeReadSize!=contract.Width || contract.Width<=0
                || TrivialConstructorRecovery.SameType(method.DeclaringType,field.Field.DeclaringType)
                || !Receiver(field.Local,field.Field.DeclaringType))continue;
            instruction.OpCode=OpCode.Call;
            instruction.SetOperands(contract.Method,result,field.Local);
            instruction.NativeReadSize=0;instruction.NativeDirectCallTarget=contract.Method.UnderlyingPointer;
            instruction.NativeVirtualDispatch=false;
            // A field read checks null at the read, including a nonvirtual API.
            // Preserve that exception location with managed callvirt, not call.
            instruction.NativeNullCheckedCall=true;
            block.CalculateBlockType();count++;
        }
        return count;
    }
}
