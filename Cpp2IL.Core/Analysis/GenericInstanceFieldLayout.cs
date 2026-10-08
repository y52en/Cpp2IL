using System.Linq;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    // Unlike the legacy open-definition layout, this path retains the declaring
    // generic instance at each inheritance level. Non-generic offsets constrain
    // the layout; unsupported sizes and open parameters are never guessed.
    public static FieldAnalysisContext? FindInheritedFieldAtOffset(TypeAnalysisContext owner, long targetOffset, int nativeWidth = 0)
    {
        if (targetOffset < 0 || targetOffset > int.MaxValue || nativeWidth < 0 || owner.IsValueType)
            return null;
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
        var pointerSize = owner.AppContext.Binary.PointerSizeBytes;
        if (pointerSize is not (4 or 8))
            return null;
        var end = 2L * pointerSize;
        FieldAnalysisContext? result = null;
        foreach (var type in hierarchy.AsEnumerable().Reverse())
        {
            var generic = type as GenericInstanceTypeAnalysisContext;
            var definition = generic?.GenericType ?? type;
            if (generic != null && (definition.Attributes & TypeAttributes.LayoutMask) != TypeAttributes.AutoLayout)
                return null; // packing/explicit layout requires separate evidence
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
                if (offset == targetOffset)
                {
                    if (nativeWidth > 0 && nativeWidth != layout.Size) return null;
                    if (result != null) return null;
                    result = field;
                }
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
    {
        // TODO support user-defined value types
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null // an arbitrary struct needs its own layout computed, bail rather than guess
        };
    }
}
