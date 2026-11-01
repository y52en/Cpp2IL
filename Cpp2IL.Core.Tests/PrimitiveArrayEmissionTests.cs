using System;
using System.IO;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class PrimitiveArrayEmissionTests
{
    [TestCase("Boolean", "ldelem.u1", "stelem.i1")]
    [TestCase("SByte", "ldelem.i1", "stelem.i1")]
    [TestCase("Byte", "ldelem.u1", "stelem.i1")]
    [TestCase("Char", "ldelem.u2", "stelem.i2")]
    [TestCase("Int16", "ldelem.i2", "stelem.i2")]
    [TestCase("UInt16", "ldelem.u2", "stelem.i2")]
    [TestCase("Int32", "ldelem.i4", "stelem.i4")]
    [TestCase("UInt32", "ldelem.u4", "stelem.i4")]
    [TestCase("Int64", "ldelem.i8", "stelem.i8")]
    [TestCase("UInt64", "ldelem.i8", "stelem.i8")]
    [TestCase("IntPtr", "ldelem.i", "stelem.i")]
    [TestCase("UIntPtr", "ldelem.i", "stelem.i")]
    [TestCase("Single", "ldelem.r4", "stelem.r4")]
    [TestCase("Double", "ldelem.r8", "stelem.r8")]
    public void PrimitiveWidthAndSignednessArePreserved(string property, string load, string store)
    {
        var module = new ModuleDefinition("PrimitiveArrayControl");
        var type = (TypeSignature)module.CorLibTypeFactory.GetType().GetProperty(property)!.GetValue(module.CorLibTypeFactory)!;
        var body = new CilMethodBody();
        IlGenerator.EmitArrayElement(body.Instructions, type, false);
        IlGenerator.EmitArrayElement(body.Instructions, type, true);
        Assert.That(body.Instructions.Count, Is.EqualTo(2));
        Assert.That(body.Instructions[0].OpCode.ToString(), Is.EqualTo(load));
        Assert.That(body.Instructions[1].OpCode.ToString(), Is.EqualTo(store));
        Assert.That(body.Instructions[0].Operand, Is.Null);
        Assert.That(body.Instructions[1].Operand, Is.Null);
    }

    [TestCase("reference")]
    [TestCase("generic")]
    [TestCase("enum")]
    [TestCase("struct")]
    public void NonPrimitiveElementsKeepExactTokens(string kind)
    {
        var module = new ModuleDefinition("TypedArrayControl");
        TypeSignature element = kind switch {
            "reference" => module.CorLibTypeFactory.String,
            "generic" => new GenericParameterSignature(GenericParameterType.Method, 0),
            _ => new TypeDefOrRefSignature(new TypeReference(module, "Fixture", kind), true)
        };
        var body = new CilMethodBody();
        IlGenerator.EmitArrayElement(body.Instructions, element, false);
        IlGenerator.EmitArrayElement(body.Instructions, element, true);
        Assert.That(body.Instructions[0].OpCode, Is.EqualTo(CilOpCodes.Ldelem));
        Assert.That(body.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Stelem));
        Assert.That(body.Instructions[0].Operand, Is.Not.Null);
        Assert.That(body.Instructions[1].Operand, Is.Not.Null);
    }

    [TestCase("Char")]
    [TestCase("Int16")]
    [TestCase("UInt32")]
    [TestCase("Single")]
    [TestCase("Double")]
    public void DetachedRoundTripRetainsValuesAndArrayExceptions(string property)
    {
        var assembly = new AssemblyDefinition("ArrayControl" + Guid.NewGuid().ToString("N"), new Version(1,0));
        var module = new ModuleDefinition("ArrayControl.dll", new AssemblyReference("mscorlib", new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Fixture", "Generated", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var element = (TypeSignature)module.CorLibTypeFactory.GetType().GetProperty(property)!.GetValue(module.CorLibTypeFactory)!;
        var method = new MethodDefinition("RoundTrip", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(element, new TypeSignature[] {new SzArrayTypeSignature(element), element}));
        owner.Methods.Add(method); method.CilMethodBody = new CilMethodBody();
        var code = method.CilMethodBody.Instructions;
        code.Add(CilOpCodes.Ldarg_0); code.Add(CilOpCodes.Ldc_I4_0); code.Add(CilOpCodes.Ldarg_1);
        IlGenerator.EmitArrayElement(code, element, true);
        code.Add(CilOpCodes.Ldarg_0); code.Add(CilOpCodes.Ldc_I4_0);
        IlGenerator.EmitArrayElement(code, element, false); code.Add(CilOpCodes.Ret);
        using var stream = new MemoryStream(); module.Write(stream);
        // Only this newly generated fixture executes, never original game/SDK code.
        var generated = Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("RoundTrip")!;
        (Type runtime, object value) = property switch {
            "Char" => (typeof(char), (object)'\uffff'), "Int16" => (typeof(short), (object)(short)-32768),
            "UInt32" => (typeof(uint), (object)uint.MaxValue), "Single" => (typeof(float), (object)-0.0f),
            _ => (typeof(double), (object)double.NaN)
        };
        var array = Array.CreateInstance(runtime, 1);
        var result = generated.Invoke(null, [array, value]);
        Assert.That(result, Is.EqualTo(value)); Assert.That(array.GetValue(0), Is.EqualTo(value));
        if (property == "Single") Assert.That(BitConverter.SingleToInt32Bits((float)result!), Is.EqualTo(unchecked((int)0x80000000)));
        Assert.That(Assert.Throws<TargetInvocationException>(() => generated.Invoke(null, [null, value]))!.InnerException,
            Is.TypeOf<NullReferenceException>());
        Assert.That(Assert.Throws<TargetInvocationException>(() => generated.Invoke(null, [Array.CreateInstance(runtime, 0), value]))!.InnerException,
            Is.TypeOf<IndexOutOfRangeException>());
    }
}
