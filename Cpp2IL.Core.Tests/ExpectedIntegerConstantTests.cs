using System;
using System.Collections.Generic;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class ExpectedIntegerConstantTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("Int32", false, 4294967295L, false)]
    [TestCase("UInt32", false, 2147483648L, false)]
    [TestCase("Int32", true, 4294967295L, false)]
    [TestCase("UInt32", true, 2147483648L, false)]
    [TestCase("Int64", false, 0L, true)]
    [TestCase("Int64", false, 1L, true)]
    [TestCase("UInt64", false, 4294967295L, true)]
    [TestCase("Int64", true, 1L, true)]
    [TestCase("UInt64", true, -1L, true)]
    [TestCase("Int32", true, 4294967296L, true)]
    public void ConstantEmissionUsesProvenUnderlyingWidthWithoutTruncatingLargerValues(string name, bool isEnum, long value, bool wide)
    {
        var assembly = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType.DeclaringAssembly;
        var primitive = assembly.GetTypeByFullName("System." + name)!;
        TypeAnalysisContext expected = primitive;
        if (isEnum)
            expected = new InjectedTypeAnalysisContext(assembly, "Test", "Value", assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public)
                { EnumUnderlyingType = primitive };
        var instruction = Emit(value, expected);
        Assert.That(instruction.OpCode, Is.EqualTo(wide ? CilOpCodes.Ldc_I8 : CilOpCodes.Ldc_I4));
        if (wide) Assert.That(instruction.Operand, Is.EqualTo(value));
        else Assert.That(instruction.Operand, Is.EqualTo(unchecked((int)value)));
    }

    [Test]
    public void EnumWithoutUnderlyingMetadataDoesNotAssumeInt32()
    {
        var assembly = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType.DeclaringAssembly;
        var unknown = new InjectedTypeAnalysisContext(assembly, "Test", "Unknown", assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public);
        Assert.That(unknown.EnumUnderlyingType, Is.Null);
        var instruction = Emit(4294967295L, unknown);
        Assert.That(instruction.OpCode, Is.EqualTo(CilOpCodes.Ldc_I8));
        Assert.That(instruction.Operand, Is.EqualTo(4294967295L));
    }

    private static CilInstruction Emit(long value, TypeAnalysisContext expected)
    {
        var module = new ModuleDefinition("Constants.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var type = new TypeDefinition("Test", "Constants", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Load", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody();
        typeof(IlGenerator).GetMethod("LoadOperand", BindingFlags.NonPublic | BindingFlags.Static)!
            .Invoke(null, [new Immediate(value), method, new Dictionary<LocalVariable, CilLocalVariable>(), method, expected]);
        Assert.That(method.CilMethodBody.Instructions.Count, Is.EqualTo(1));
        return method.CilMethodBody.Instructions[0];
    }
}
