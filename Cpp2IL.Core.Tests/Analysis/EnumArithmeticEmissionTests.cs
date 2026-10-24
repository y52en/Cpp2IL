using System.Reflection;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class EnumArithmeticEmissionTests
{
    [TestCase("Byte", "Int32", 4)]
    [TestCase("SByte", "Int32", 4)]
    [TestCase("Int16", "UInt32", 4)]
    [TestCase("UInt16", "Int32", 4)]
    [TestCase("Int32", "Int32", 4)]
    [TestCase("UInt32", "Int32", 4)]
    [TestCase("Int64", "Int64", 8)]
    [TestCase("UInt64", "Int64", 8)]
    [TestCase("Int64", "UInt64", 8)]
    [TestCase("Int32", "Int64", 0)]
    [TestCase("Int64", "Int32", 0)]
    [TestCase("Int32", "Single", 0)]
    [TestCase("Int32", "Boolean", 0)]
    [TestCase("Int32", "Object", 0)]
    [TestCase("Int32", null, 0)]
    [TestCase(null, "Int32", 0)]
    public void OnlyMetadataProvenSameStackWidthIsConverted(string? underlying, string? expected, int width)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var enumeration = new InjectedTypeAnalysisContext(assembly, "Test", "NumericEnum",
            assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public)
        { EnumUnderlyingType = underlying == null ? null : assembly.GetTypeByFullName("System." + underlying) };
        var operand = new LocalVariable("value", new Register(null, "X0"), enumeration);
        var conversion = IlGenerator.EnumArithmeticConversion(operand,
            expected == null ? null : assembly.GetTypeByFullName("System." + expected));
        Assert.That(conversion, Is.EqualTo(width == 4 ? CilOpCodes.Conv_I4 : width == 8 ? CilOpCodes.Conv_I8 : (CilOpCode?)null));
        Assert.That(operand.Type, Is.SameAs(enumeration));
    }

    [Test]
    public void PlainIntegerAndUnknownOperandsAreNotConverted()
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        foreach (var operand in new IOperand[] { new Immediate(1),
            new LocalVariable("integer", new Register(null, "X0"), types.SystemInt32Type),
            new LocalVariable("unknown", new Register(null, "X1")) })
            Assert.That(IlGenerator.EnumArithmeticConversion(operand, types.SystemInt32Type), Is.Null);
    }
}
