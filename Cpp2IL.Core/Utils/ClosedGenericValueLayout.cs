using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

/// <summary>Closed, unpacked sequential generic value storage; never guess an open T.</summary>
public static class ClosedGenericValueLayout
{
    public sealed record FieldStorage(FieldAnalysisContext Field,long Offset,long Size);

    // Return a per-instantiation view, never overwrite the generic definition's
    // shared zero metadata offsets. The complete layout must pass the same
    // closed/default-packed/native-size proof as the existing ABI size path.
    public static IReadOnlyList<FieldStorage>? Fields(TypeAnalysisContext type,int pointerSize)
    {
        if(type is not GenericInstanceTypeAnalysisContext generic || !type.IsValueType
            || TryGet(type,pointerSize) is not { } complete)return null;
        var fields=new List<FieldStorage>();long end=0;
        foreach(var original in generic.GenericType.Fields.Where(f=>!f.IsStatic
            && (f.Attributes&FieldAttributes.Literal)==0))
        {
            var field=new ConcreteGenericFieldAnalysisContext(original,generic);
            if(Layout(field.FieldType,pointerSize,new HashSet<TypeAnalysisContext>()) is not { } storage)return null;
            var offset=(end+storage.Alignment-1)&~(storage.Alignment-1);
            fields.Add(new(field,offset,storage.Size));end=offset+storage.Size;
        }
        return ((end+complete.Alignment-1)&~(complete.Alignment-1))==complete.Size?fields:null;
    }

    public static (long Size, long Alignment)? TryGet(TypeAnalysisContext type, int pointerSize)
    {
        // This recovery's metadata/ABI evidence is the ARM64/x64 layout only.
        if (pointerSize != 8 || type is not GenericInstanceTypeAnalysisContext) return null;
        var layout = Layout(type, pointerSize, new HashSet<TypeAnalysisContext>());
        // The existing HFA resolver only handles flat nongeneric metadata.
        // Do not let a known byte count misclassify a possibly homogeneous
        // floating aggregate's return ABI. Its generic HFA needs separate proof.
        return layout is { HasNonFloatingLeaf: true } known ? (known.Size, known.Alignment) : null;
    }

    private static (long Size, long Alignment, bool HasNonFloatingLeaf)? Layout(TypeAnalysisContext type, int pointerSize,
        HashSet<TypeAnalysisContext> active)
    {
        if (type is GenericParameterTypeAnalysisContext or ByRefTypeAnalysisContext
            || type.HasAnyGenericParameters()) return null;
        if (!type.IsValueType) return (pointerSize, pointerSize, true);
        (long Size, long Alignment, bool HasNonFloatingLeaf)? scalar = type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1, true),
            "System.Char" or "System.Int16" or "System.UInt16" => (2, 2, true),
            "System.Int32" or "System.UInt32" => (4, 4, true),
            "System.Int64" or "System.UInt64" => (8, 8, true),
            "System.Single" => (4, 4, false),
            "System.Double" => (8, 8, false),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize, true),
            _ => null
        };
        if (scalar != null) return scalar;
        if (active.Count >= 16 || !active.Add(type)) return null;
        try
        {
            var generic = type as GenericInstanceTypeAnalysisContext;
            var definition = generic?.GenericType ?? type;
            if (type.IsEnumType && definition.Fields.SingleOrDefault(f => !f.IsStatic) is { } underlying)
                return Layout(underlying.FieldType, pointerSize, active);
            var metadata = definition.Definition;
            var layoutKind = definition.Attributes & TypeAttributes.LayoutMask;
            if (metadata == null || layoutKind != TypeAttributes.SequentialLayout
                    && !(generic == null && layoutKind == TypeAttributes.AutoLayout)
                || metadata.PackingSize != 0 || metadata.SpecifiedPackingSize != 0
                || (generic != null && !metadata.ClassSizeIsDefault && metadata.Size is not (0 or -1))
                || generic != null && generic.GenericArguments.Count != definition.GenericParameters.Count)
                return null;
            if (definition.BaseType is not { FullName: "System.ValueType" }) return null;
            var fields = definition.Fields.Where(f => !f.IsStatic && (f.Attributes & FieldAttributes.Literal) == 0).ToArray();
            if (fields.Length is 0 or > 512) return null;
            long end = 0, alignment = 1;
            var nonFloating = false;
            foreach (var original in fields)
            {
                var field = generic == null ? original : new ConcreteGenericFieldAnalysisContext(original, generic);
                if (Layout(field.FieldType, pointerSize, active) is not { } layout) return null;
                var offset = (end + layout.Alignment - 1) & ~(layout.Alignment - 1);
                if (offset > int.MaxValue - layout.Size || generic == null && field.Offset != offset) return null;
                end = offset + layout.Size;
                alignment = Math.Max(alignment, layout.Alignment);
                nonFloating |= layout.HasNonFloatingLeaf;
            }
            var size = (end + alignment - 1) & ~(alignment - 1);
            // Concrete nongeneric metadata offsets/total size constrain nested
            // structs. Generic-definition zero offsets are NOT treated as layout.
            if (generic == null && (metadata.RawSizes.instance_size < 2L * pointerSize
                || metadata.RawSizes.instance_size - 2L * pointerSize != size)) return null;
            return (size, alignment, nonFloating);
        }
        finally { active.Remove(type); }
    }
}
