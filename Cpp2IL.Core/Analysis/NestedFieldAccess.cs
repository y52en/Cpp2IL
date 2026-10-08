using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

public static class NestedFieldAccess
{
    // A native byte range distinguishes a whole struct store from a scalar
    // store to its first field at exactly the same address.
    public static FieldReference? Find(TypeAnalysisContext owner,LocalVariable root,long offset,int width)
        => Find(owner,root,offset,width,null,new HashSet<TypeAnalysisContext>(),8);

    private static FieldReference? Find(TypeAnalysisContext owner,LocalVariable root,long offset,int width,FieldReference? parent,HashSet<TypeAnalysisContext> seen,int remaining)
    {
        if(width<=0 || remaining<=0 || !seen.Add(owner)) return null;
        var fields=new List<FieldAnalysisContext>();
        for(var type=owner;type!=null;type=type.BaseType)
            fields.AddRange(type.Fields.Where(f=>!f.IsStatic && (f.Attributes&FieldAttributes.Literal)==0 && f.Offset>=0));
        var matches=fields.Where(f=>f.FieldType.IsValueType && TypeSizes.UnboxedSize(f.FieldType,8) is var size
            && size>0 && offset>=f.Offset && offset+width<=f.Offset+size).ToArray();
        if(matches.Length!=1) return null;
        var field=matches[0];var delta=offset-field.Offset;
        var access=new FieldReference(field,root,(int)offset){Parent=parent};
        if(delta==0 && TypeSizes.UnboxedSize(field.FieldType,8)==width) return access;
        return Find(field.FieldType,root,delta,width,access,seen,remaining-1);
    }
}
