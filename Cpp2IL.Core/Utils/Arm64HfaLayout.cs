using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class Arm64HfaLayout
{
    // Only exact, flat metadata layouts. Nested/overlapping/padded layouts need
    // separate proof; ordinary structs must never be mistaken for an HFA.
    public static FieldAnalysisContext[]? Fields(TypeAnalysisContext type)
    {
        if(!type.IsValueType || type.IsEnumType || BaseCallingConventionResolver.IsFloatingPoint(type)) return null;
        var fields=type.Fields.Where(f=>!f.IsStatic).OrderBy(f=>f.Offset).ToArray();
        if(fields.Length is <1 or >4) return null;
        var scalar=fields[0].FieldType;
        if(!BaseCallingConventionResolver.IsFloatingPoint(scalar) || fields.Any(f=>f.FieldType!=scalar)) return null;
        var width=scalar==type.AppContext.SystemTypes.SystemSingleType?4:8;
        if(TypeSizes.UnboxedSize(type,8)!=fields.Length*width) return null;
        for(var i=0;i<fields.Length;i++) if(fields[i].Offset!=i*width) return null;
        return fields;
    }
}
