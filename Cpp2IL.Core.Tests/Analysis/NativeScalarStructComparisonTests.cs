using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeScalarStructComparisonTests
{
    private sealed class Getter(TypeAnalysisContext owner, TypeAnalysisContext returned)
        : InjectedMethodAnalysisContext(owner, "get_Payload", returned,
            MethodAttributes.Public | MethodAttributes.SpecialName, [])
    { public override ulong UnderlyingPointer => 0x1000; }

    private static (InjectedTypeAnalysisContext Owner, FieldAnalysisContext Field, Getter Getter,
        NativeFieldLoadProofs.Entry Proof) Fixture(int width, bool unsigned = false)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var scalar = width == 8 ? unsigned ? types.SystemUInt64Type : types.SystemInt64Type
            : unsigned ? types.SystemUInt32Type : types.SystemInt32Type;
        var owner = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly, "Fixture", "Scalar",
            types.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed);
        var field = owner.InjectFieldContext("payload", scalar, FieldAttributes.Private); field.Offset = 0;
        var getter = new Getter(owner, scalar); owner.Methods.Add(getter);
        owner.InjectPropertyContext("Payload", scalar, getter, null, PropertyAttributes.None);
        var bytes = BitConverter.GetBytes(width == 8 ? 0xf9400800u : 0xb9401000u).Concat(BitConverter.GetBytes(0xd65f03c0u)).ToArray();
        return (owner, field, getter, new(bytes, NativeFieldLoadProofs.Decode(bytes)!));
    }

    [TestCase(4, false)] [TestCase(4, true)]
    [TestCase(8, false)] [TestCase(8, true)]
    public void CompleteOriginalBoxedGetterSelectsOnlyTheSameIntegralPayload(int width, bool unsigned)
    {
        var f = Fixture(width, unsigned);
        Assert.That(NativeScalarStructComparison.Prove(f.Getter, f.Field, width, f.Proof, true), Is.SameAs(f.Getter));
    }

    [TestCase("unknown-native-width")] [TestCase("wrong-native-width")]
    [TestCase("nonoriginal-field")] [TestCase("two-instance-fields")]
    [TestCase("nonzero-offset")] [TestCase("private-getter")]
    [TestCase("static-getter")] [TestCase("virtual-getter")]
    [TestCase("synchronized-getter")] [TestCase("wrong-return")]
    [TestCase("missing-property")] [TestCase("ambiguous-property")]
    [TestCase("modified-native-return")] [TestCase("mismatched-native-effects")]
    [TestCase("nonpublic-owner")]
    public void MissingOrConflictingEvidenceDoesNotInventAnOperator(string shape)
    {
        var f = Fixture(8); var getter = f.Getter; var proof = f.Proof;
        int width = shape == "unknown-native-width" ? 0 : shape == "wrong-native-width" ? 4 : 8;
        if (shape == "two-instance-fields") f.Owner.InjectFieldContext("other", f.Field.FieldType, FieldAttributes.Private).Offset = 8;
        if (shape == "nonzero-offset") f.Field.Offset = 8;
        if (shape == "private-getter") getter.Attributes = MethodAttributes.Private;
        if (shape == "static-getter") getter.Attributes |= MethodAttributes.Static;
        if (shape == "virtual-getter") getter.Attributes |= MethodAttributes.Virtual;
        if (shape == "synchronized-getter") getter.ImplAttributes |= MethodImplAttributes.Synchronized;
        if (shape == "wrong-return") getter = new Getter(f.Owner, f.Owner.AppContext.SystemTypes.SystemInt32Type);
        if (shape == "missing-property") f.Owner.Properties.Clear();
        if (shape == "ambiguous-property") f.Owner.InjectPropertyContext("Alias", f.Field.FieldType, getter, null, PropertyAttributes.None);
        if (shape == "nonpublic-owner") f.Owner.Attributes = TypeAttributes.NotPublic;
        if (shape == "modified-native-return") {var bytes = proof.Bytes.ToArray(); bytes[^1] ^= 1; proof = new(bytes, proof.Reads);}
        if (shape == "mismatched-native-effects") proof = new(proof.Bytes, [new("gpr", 0, 8, 24, 0)]);
        Assert.That(NativeScalarStructComparison.Prove(getter, f.Field, width, proof, shape != "nonoriginal-field"), Is.Null);
    }

    [TestCase(0)] [TestCase(1)] [TestCase(2)] [TestCase(16)]
    public void UnknownOrUnsupportedNativeComparisonWidthDoesNotLoadProofs(int width)
    {
        var f = Fixture(8);
        Assert.That(NativeScalarStructComparison.Find(f.Owner, width), Is.Null);
    }
}
