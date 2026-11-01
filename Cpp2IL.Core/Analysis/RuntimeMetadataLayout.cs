using AssetRipper.Primitives;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>Offsets used to read native runtime metadata, never managed instance fields.</summary>
public readonly record struct RuntimeMetadataLayout(
    long InitializedFlag, long VTable, long MethodClass, long MethodRgctx,
    long ClassRgctx, long StaticFields)
{
    public static RuntimeMetadataLayout For(MethodAnalysisContext method)
        => For(method.AppContext.UnityVersion, method.AppContext.Binary.PointerSizeBytes);

    public static RuntimeMetadataLayout For(UnityVersion version, int pointerSize)
    {
        // Verified against Unity 2018.4 headers and the matching ARM64 binary.
        // Do not extend this to other versions/architectures merely by subtracting offsets.
        if (pointerSize == 8 && version.Major == 2018 && version.Minor == 4)
            return new(0x126, 0x128, 0x18, 0x30, 0xC0, 0xB8);

        // Preserve upstream's existing layout assumptions outside the verified profile.
        return pointerSize == 4
            ? new(0xBD, 0xC0, 0x10, 0x1C, 0x60, 0x5C)
            : new(0x135, 0x138, 0x20, 0x38, 0xC0, 0xB8);
    }
}
