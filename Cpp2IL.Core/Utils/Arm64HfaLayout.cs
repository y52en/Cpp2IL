using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class Arm64HfaLayout
{
    // Offset is relative to the complete aggregate; Field/Path remain original
    // metadata identities, not injected pseudo-fields that alter type layouts.
    public sealed record Lane(FieldAnalysisContext Field,long Offset,FieldAnalysisContext[] Path)
    {
        public TypeAnalysisContext FieldType=>Field.FieldType;
    }

    public static Lane[]? Fields(TypeAnalysisContext type)=>Fields(type,t=>TypeSizes.UnboxedSize(t,8));

    // AAPCS64 homogeneous aggregates may contain nested homogeneous aggregates.
    // Prove every byte and scalar leaf; padding, overlap, mixed types, unknown
    // sizes, open generics and recursive metadata are deliberately rejected.
    internal static Lane[]? Fields(TypeAnalysisContext type,Func<TypeAnalysisContext,long> size)
    {
        if(BaseCallingConventionResolver.IsFloatingPoint(type))return null;
        var lanes=new List<Lane>();var seen=new HashSet<TypeAnalysisContext>();
        bool Visit(TypeAnalysisContext current,long offset,FieldAnalysisContext[] path)
        {
            if(!current.IsValueType || current.IsEnumType || current.HasAnyGenericParameters()
                || path.Length>8 || !seen.Add(current))return false;
            var fields=current.Fields.Where(f=>!f.IsStatic).OrderBy(f=>f.Offset).ToArray();
            if(fields.Length is <1 or >4 || size(current) is <=0 or >32)return false;
            long end=0;
            foreach(var field in fields)
            {
                if(field.Offset!=end)return false;
                var nested=field.FieldType;var next=path.Append(field).ToArray();
                if(BaseCallingConventionResolver.IsFloatingPoint(nested))
                {
                    var width=ReferenceEquals(nested,current.AppContext.SystemTypes.SystemSingleType)?4:8;
                    if(lanes.Count>=4 || lanes.Any(l=>!ReferenceEquals(l.FieldType,nested)))return false;
                    lanes.Add(new(field,offset+end,next));end+=width;
                }
                else
                {
                    if(!Visit(nested,offset+end,next))return false;
                    end+=size(nested);
                }
            }
            seen.Remove(current);
            return end==size(current);
        }
        return Visit(type,0,[]) && lanes.Count is >=1 and <=4?lanes.ToArray():null;
    }
}
