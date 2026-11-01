using System;

namespace Cpp2IL.Core.Analysis;

// Effect equivalence only. This does not resolve managed ownership, public
// accessor identity, caller receiver ABI or authorize a call rewrite.
internal static class NativeMaskedReceiverPairShape
{
    internal static bool Equivalent(ReadOnlySpan<byte> boxed,ReadOnlySpan<byte> unboxed,int header)
    {
        if(header!=16 || NativeMaskedScalarGetterShape.Decode(boxed) is not {} a
            || NativeMaskedScalarGetterShape.Decode(unboxed) is not {} b
            || a.Width!=b.Width || a.Mask!=b.Mask || a.Offset!=b.Offset+header)return false;
        // Preserve every other bit, including destination/scratch registers and
        // their clobbers. Only the unsigned load displacement may differ.
        var x=BitConverter.ToUInt32(boxed.Slice(0,4));var y=BitConverter.ToUInt32(unboxed.Slice(0,4));
        return (x&~0x003ffc00u)==(y&~0x003ffc00u) && boxed.Slice(4).SequenceEqual(unboxed.Slice(4));
    }
}
