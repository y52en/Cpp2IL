using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

// Native facts belong to ONE metadata method entry, not globally to open T.
// Every known alias must be a complete instantiation of that exact definition
// and agree on the entire closed return ABI and every field's storage kind.
public static class SharedGenericReturnLayout
{
    public sealed record Profile(long Size,long Alignment,
        IReadOnlyList<ClosedGenericValueLayout.FieldStorage> Fields,int ConcreteAliases);

    public static IReadOnlyList<ClosedGenericValueLayout.FieldStorage>? FieldsFor(MethodAnalysisContext method,TypeAnalysisContext owner)
        => ReferenceEquals(method.ReturnType,owner)?TryGet(method)?.Fields:null;

    public static Profile? TryGet(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.UnderlyingPointer==0
            || !method.AppContext.MethodsByAddress.TryGetValue(method.UnderlyingPointer,out var aliases))return null;
        return TryFromAliases(method,aliases,method.AppContext.Binary.PointerSizeBytes);
    }

    public static Profile? TryFromAliases(MethodAnalysisContext method,IReadOnlyList<MethodAnalysisContext> aliases,int pointerSize)
    {
        if(pointerSize!=8 || method is ConcreteGenericMethodAnalysisContext
            || method.ReturnType is not GenericInstanceTypeAnalysisContext {IsValueType:true} open
            || !open.HasAnyGenericParameters() || aliases.Count<2
            || aliases.Distinct().Count()!=aliases.Count
            || aliases.Count(m=>ReferenceEquals(m,method))!=1)return null;
        var closed=new List<(GenericInstanceTypeAnalysisContext Type,long Size,long Alignment,
            IReadOnlyList<ClosedGenericValueLayout.FieldStorage> Fields)>();
        foreach(var alias in aliases)
        {
            if(ReferenceEquals(alias,method))continue;
            if(alias is not ConcreteGenericMethodAnalysisContext generic
                || !ReferenceEquals(generic.BaseMethodContext,method)
                || alias.ReturnType is not GenericInstanceTypeAnalysisContext returned
                || !ReferenceEquals(returned.GenericType,open.GenericType)
                || returned.HasAnyGenericParameters()
                || ClosedGenericValueLayout.TryGet(returned,8) is not {Size:>16} layout
                || ClosedGenericValueLayout.Fields(returned,8) is not { } fields)return null;
            closed.Add((returned,layout.Size,layout.Alignment,fields));
        }
        if(closed.Count==0)return null;
        var first=closed[0];
        foreach(var other in closed)
        {
            if(other.Size!=first.Size || other.Alignment!=first.Alignment || other.Fields.Count!=first.Fields.Count)return null;
            for(var i=0;i<first.Fields.Count;i++)
            {
                var left=first.Fields[i];var right=other.Fields[i];
                if(left.Offset!=right.Offset || left.Size!=right.Size
                    || !ReferenceEquals(Base(left.Field),Base(right.Field))
                    || !SameStorageKind(left.Field.FieldType,right.Field.FieldType,0))return null;
            }
        }
        var result=first.Fields.Select(f=>new ClosedGenericValueLayout.FieldStorage(
            new ConcreteGenericFieldAnalysisContext(Base(f.Field),open),f.Offset,f.Size)).ToArray();
        return new(first.Size,first.Alignment,result,closed.Count);
    }

    private static FieldAnalysisContext Base(FieldAnalysisContext field)
        => field is ConcreteGenericFieldAnalysisContext concrete?concrete.BaseFieldContext:field;

    private static bool SameStorageKind(TypeAnalysisContext left,TypeAnalysisContext right,int depth)
    {
        if(depth>=16 || left.HasAnyGenericParameters() || right.HasAnyGenericParameters()
            || left is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
            || right is PointerTypeAnalysisContext or ByRefTypeAnalysisContext)return false;
        if(left.IsValueType!=right.IsValueType)return false;
        if(!left.IsValueType)return true;
        if(left is not GenericInstanceTypeAnalysisContext a)
            return ReferenceEquals(left,right);
        if(right is not GenericInstanceTypeAnalysisContext b
            || !ReferenceEquals(a.GenericType,b.GenericType)
            || ClosedGenericValueLayout.TryGet(a,8) is not { } la
            || ClosedGenericValueLayout.TryGet(b,8) is not { } lb || la!=lb
            || ClosedGenericValueLayout.Fields(a,8) is not { } fa
            || ClosedGenericValueLayout.Fields(b,8) is not { } fb || fa.Count!=fb.Count)return false;
        for(var i=0;i<fa.Count;i++)
            if(fa[i].Offset!=fb[i].Offset || fa[i].Size!=fb[i].Size
                || !ReferenceEquals(Base(fa[i].Field),Base(fb[i].Field))
                || !SameStorageKind(fa[i].Field.FieldType,fb[i].Field.FieldType,depth+1))return false;
        return true;
    }
}
