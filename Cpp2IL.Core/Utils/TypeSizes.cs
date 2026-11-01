using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class TypeSizes
{
    public static bool IsScalarValueType(TypeAnalysisContext type) => type.IsEnumType || type.FullName is
        "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char" or "System.Int16" or "System.UInt16"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.Single" or "System.Double"
        or "System.IntPtr" or "System.UIntPtr";

    // Unboxed size of a value type, so the metadata's boxed size - the two pointer fields in the header. 0 if we
    // don't know (no definition, e.g. an open generic).
    public static long UnboxedSize(TypeAnalysisContext type, int pointerSize)
    {
        var header = 2L * pointerSize;

        if (type.Definition?.RawSizes is { instance_size: var boxed } && boxed > header)
            return boxed - header;

        if (ClosedGenericValueLayout.TryGet(type, pointerSize) is { } closed)
            return closed.Size;

        return 0;
    }
}
