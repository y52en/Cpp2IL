using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

public static class NestedFieldAccess
{
    // A native byte range distinguishes a whole struct store from a scalar
    // store to its first field at exactly the same address.
    public static FieldReference? Find(TypeAnalysisContext owner,LocalVariable root,long offset,int width,MethodAnalysisContext? nativeMethod=null)
        => Find(owner,root,offset,width,null,new HashSet<TypeAnalysisContext>(),8,nativeMethod);

    private static FieldReference? Find(TypeAnalysisContext owner,LocalVariable root,long offset,int width,FieldReference? parent,HashSet<TypeAnalysisContext> seen,int remaining,MethodAnalysisContext? nativeMethod)
    {
        if(width<=0 || remaining<=0 || offset<0 || offset>long.MaxValue-width
            || owner.AppContext.Binary.PointerSizeBytes!=8 || !seen.Add(owner)) return null;
        var fields=new List<(FieldAnalysisContext Field,long Offset,long Size)>();
        for(var type=owner;type!=null;type=type.BaseType)
        {
            if(type is GenericInstanceTypeAnalysisContext && type.IsValueType)
            {
                var layout=ClosedGenericValueLayout.Fields(type,8)
                    ??(nativeMethod==null?null:SharedGenericReturnLayout.FieldsFor(nativeMethod,type));
                if(layout==null)return null;
                fields.AddRange(layout.Select(f=>(f.Field,f.Offset,f.Size)));
            }
            else fields.AddRange(type.Fields.Where(f=>!f.IsStatic
                && (f.Attributes&FieldAttributes.Literal)==0 && f.Offset>=0)
                .Select(f=>(f,(long)f.Offset,StorageSize(f.FieldType))));
        }
        var matches=fields.Where(f=>f.Size>0 && offset>=f.Offset && offset+width<=f.Offset+f.Size).ToArray();
        if(matches.Length!=1) return null;
        var field=matches[0].Field;var delta=offset-matches[0].Offset;
        var access=new FieldReference(field,root,(int)offset){Parent=parent};
        // A reference INSIDE a proven inline value type is an exact pointer
        // slot, not another embedded object layout. Never descend through it
        // or reinterpret a partial pointer read as a managed reference.
        if(!field.FieldType.IsValueType)
            return (parent!=null || owner.IsValueType) && delta==0 && width==8 ? access : null;
        if(delta==0 && TypeSizes.UnboxedSize(field.FieldType,8)==width) return access;
        return Find(field.FieldType,root,delta,width,access,seen,remaining-1,nativeMethod);
    }

    private static long StorageSize(TypeAnalysisContext type)
    {
        if(type.IsValueType) return TypeSizes.UnboxedSize(type,8);
        return !type.HasAnyGenericParameters() && type.Type is
            Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_STRING
            or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
            or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST ? 8 : 0;
    }
}
