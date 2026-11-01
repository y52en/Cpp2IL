using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Native-width comparisons of a one-field integral value must compare its
// payload, not emit CLI ceq on a struct. Reuse an actual public getter only
// after complete original load/RET bytes and metadata prove that same payload.
internal static class NativeScalarStructComparison
{
    internal static int Width(TypeAnalysisContext type) => type.FullName switch {
        "System.Int32" or "System.UInt32" => 4,
        "System.Int64" or "System.UInt64" => 8,
        _ => 0
    };

    internal static MethodAnalysisContext? Prove(MethodAnalysisContext getter, FieldAnalysisContext field,
        int size, NativeFieldLoadProofs.Entry proof, bool originalField)
    {
        var owner = field.DeclaringType;
        if (!originalField || !owner.IsValueType || owner.IsEnumType || TypeSizes.IsScalarValueType(owner)
            || owner.IsGenericInstance || owner.HasAnyGenericParameters()
            || (owner.Attributes & TypeAttributes.VisibilityMask) is not (TypeAttributes.Public or TypeAttributes.NestedPublic)
            || owner.Fields.Count(f => !f.IsStatic) != 1 || field.IsStatic || field.Offset != 0
            || Width(field.FieldType) != size || size is not (4 or 8)
            || !ReferenceEquals(getter.DeclaringType, owner) || getter.IsStatic || getter.IsVirtual
            || getter.Visibility != MethodAttributes.Public || getter.Parameters.Count != 0 || getter.GenericParameters.Count != 0
            || getter.UnderlyingPointer == 0 || ((int)getter.ImplAttributes & 0x1027) != 0
            || ((int)getter.Attributes & 0x6000) != 0
            || !TrivialConstructorRecovery.SameType(getter.ReturnType, field.FieldType)
            || owner.Properties.Count(p => ReferenceEquals(p.Getter, getter)) != 1
            || proof.Bytes.Length != 8 || NativeFieldLoadProofs.Decode(proof.Bytes) is not { Length: 1 } actual
            || proof.Reads.Length != 1 || proof.Reads[0] != actual[0]) return null;
        var read = actual[0];
        return read.Kind == "gpr" && read.Register == 0 && read.Width == size
            && read.Offset == 16 && read.Instruction == 0 ? getter : null;
    }

    internal static MethodAnalysisContext? Find(TypeAnalysisContext type, int nativeWidth)
    {
        if (nativeWidth is not (4 or 8) || !type.IsValueType || type.IsEnumType
            || type.IsGenericInstance || type.HasAnyGenericParameters()
            || TypeSizes.UnboxedSize(type, 8) != nativeWidth) return null;
        var fields = type.Fields.Where(f => !f.IsStatic).ToArray();
        if (fields.Length != 1 || fields[0].BackingData == null) return null;
        var proofs = NativeFieldLoadProofs.For(type.AppContext);
        var matches = type.Methods.Where(m => m.UnderlyingPointer != 0
            && proofs.TryGetValue(m.UnderlyingPointer, out var proof)
            && Prove(m, fields[0], nativeWidth, proof, true) != null).ToArray();
        return matches.Length == 1 ? matches[0] : null;
    }
}
