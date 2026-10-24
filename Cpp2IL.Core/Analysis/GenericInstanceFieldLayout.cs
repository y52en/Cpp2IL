using System.Linq;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    public sealed record FieldStorage(FieldAnalysisContext Field,long Offset,long Size);
    // Unlike the legacy open-definition layout, this path retains the declaring
    // generic instance at each inheritance level. Non-generic offsets constrain
    // the layout; unsupported sizes and open parameters are never guessed.
    public static FieldAnalysisContext? FindInheritedFieldAtOffset(TypeAnalysisContext owner, long targetOffset, int nativeWidth = 0)
    {
        if(targetOffset<0 || targetOffset>int.MaxValue || nativeWidth<0)return null;
        var matches=InheritedFields(owner)?.Where(f=>f.Offset==targetOffset
            && (nativeWidth==0 || nativeWidth==f.Size)).ToArray();
        return matches is {Length:1}?matches[0].Field:null;
    }

    // A per-instantiation view, never write recomputed offsets back to the
    // shared generic definition. Component access needs the WHOLE proven range.
    public static IReadOnlyList<FieldStorage>? InheritedFields(TypeAnalysisContext owner)
    {
        if(owner.IsValueType)return null;
        var hierarchy = new List<TypeAnalysisContext>();
        var seen = new HashSet<string>();
        for (var type = owner; type != null; type = type.BaseType)
        {
            if (hierarchy.Count >= 64 || !seen.Add(type.FullName))
                return null;
            hierarchy.Add(type);
        }
        if (!hierarchy.Any(t => t is GenericInstanceTypeAnalysisContext))
            return null;
        if(!ReferenceEquals(hierarchy[^1],owner.AppContext.SystemTypes.SystemObjectType))return null;
        var pointerSize = owner.AppContext.Binary.PointerSizeBytes;
        if (pointerSize is not (4 or 8))
            return null;
        var end = 2L * pointerSize;
        var result=new List<FieldStorage>();
        foreach (var type in hierarchy.AsEnumerable().Reverse())
        {
            var generic = type as GenericInstanceTypeAnalysisContext;
            var definition = generic?.GenericType ?? type;
            if (generic != null && (definition.Attributes & TypeAttributes.LayoutMask) != TypeAttributes.AutoLayout)
                return null; // packing/explicit layout requires separate evidence
            if(generic!=null && definition.Definition is {} metadata
                && (metadata.PackingSize!=0 || metadata.SpecifiedPackingSize!=0
                    || !metadata.ClassSizeIsDefault && metadata.Size is not (0 or -1)))return null;
            foreach (var original in definition.Fields.Where(f => !f.IsStatic && (f.Attributes & FieldAttributes.Literal) == 0))
            {
                FieldAnalysisContext field = generic == null ? original : new ConcreteGenericFieldAnalysisContext(original, generic);
                if (field.FieldType.HasAnyGenericParameters()
                    || GetSizeAndAlignment(field.FieldType, pointerSize) is not { } layout)
                    return null;
                var aligned = (end + layout.Alignment - 1) & ~(layout.Alignment - 1);
                var offset = generic == null ? original.Offset : aligned;
                if (offset < aligned || offset > long.MaxValue - layout.Size)
                    return null;
                result.Add(new(field,offset,layout.Size));
                end = offset + layout.Size;
            }
        }
        return result;
    }

    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        // TODO Support anything outside the trivial case.
        for (var baseType = definition.BaseType; baseType != null; baseType = baseType.BaseType)
            if (baseType.Fields.Any(f => !f.IsStatic))
                return null;

        var offset = 2L * pointerSize;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(field.FieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize)
        => GetSizeAndAlignment(fieldType, pointerSize, new HashSet<TypeAnalysisContext>());

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize,
        HashSet<TypeAnalysisContext> active)
    {
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize);

        (long Size, long Alignment)? primitive = fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null
        };
        if (primitive != null) return primitive;

        // Derive storage only from a closed, default-packed sequential metadata
        // layout. Validate every offset and the complete unboxed size; neither
        // a type name nor a guessed pointer-sized generic argument is evidence.
        var definition = fieldType.Definition;
        if (definition == null || fieldType.HasAnyGenericParameters()
            || (fieldType.Attributes & TypeAttributes.LayoutMask) != TypeAttributes.SequentialLayout
            || !definition.PackingSizeIsDefault && definition.PackingSize!=0
            || definition.SpecifiedPackingSize != 0 || active.Count >= 16 || !active.Add(fieldType))
            return null;
        try
        {
            long end = 0, alignment = 1;
            var fields = fieldType.Fields.Where(f => !f.IsStatic && (f.Attributes & FieldAttributes.Literal) == 0).ToArray();
            if (fields.Length == 0) return null;
            foreach (var field in fields)
            {
                if (GetSizeAndAlignment(field.FieldType, pointerSize, active) is not { } layout)
                    return null;
                var offset = (end + layout.Alignment - 1) & ~(layout.Alignment - 1);
                if (field.Offset != offset || offset > int.MaxValue - layout.Size) return null;
                end = offset + layout.Size;
                alignment = System.Math.Max(alignment, layout.Alignment);
            }
            var size = (end + alignment - 1) & ~(alignment - 1);
            // Explicit sequential Size is not uncertainty when ALL offsets,
            // natural footprint and native unboxed size independently agree.
            // Extra declared padding remains unsupported rather than guessed.
            return CompleteValueSizeAgrees(definition.Size,size,TypeSizes.UnboxedSize(fieldType,pointerSize))
                ? (size, alignment) : null;
        }
        finally { active.Remove(fieldType); }
    }

    internal static bool CompleteValueSizeAgrees(long declared,long computed,long native)
        => computed>0 && native==computed && (declared is 0 or -1 || declared==computed);
}
