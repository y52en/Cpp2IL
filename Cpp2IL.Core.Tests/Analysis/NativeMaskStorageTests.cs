using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeMaskStorageTests
{
    [TestCase("array-length", true)]
    [TestCase("commuted", true)]
    [TestCase("low-mask", true)]
    [TestCase("unsigned-result", true)]
    [TestCase("scalar-input", true)]
    [TestCase("wide-mask", false)]
    [TestCase("wide-result", false)]
    [TestCase("opaque-consumer", false)]
    [TestCase("pointer-consumer", false)]
    [TestCase("i8-consumer", false)]
    [TestCase("reference-consumer", false)]
    [TestCase("float-operation", false)]
    public void Low32BitExtractionDoesNotConfusePhysicalWidthWithConsistentI4Storage(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var array = new LocalVariable("array", new(null, "X19"), new SzArrayTypeAnalysisContext(t.SystemInt32Type));
        var input = new LocalVariable("length", new(null, "X22"));
        var resultType = shape == "wide-result" ? t.SystemInt64Type : shape == "unsigned-result" ? t.SystemUInt32Type : t.SystemInt32Type;
        var result = new LocalVariable("result", new(null, "X20"), resultType);
        IOperand mask = new Immediate(shape == "wide-mask" ? 0x3fffffffffffffffL : shape == "low-mask" ? 255 : uint.MaxValue);
        var operation = new Instruction(1, OpCode.And, result,
            shape == "commuted" ? mask : input, shape == "commuted" ? input : mask)
            { NativeArithmeticSize = 8, NativeFloatingPointSize = shape == "float-operation" ? 8 : 0 };
        var steps = new List<Instruction> { new(0, OpCode.Move, input, shape == "scalar-input"
            ? new LocalVariable("scalar", new(null, "X0"), t.SystemInt32Type) : new ArrayLength(array)), operation };
        if (shape == "opaque-consumer") steps.Add(new(2, OpCode.CallVoid, new StringLiteral("opaque"), input));
        if (shape == "pointer-consumer") steps.Add(new Instruction(2, OpCode.Move,
            new LocalVariable("read", new(null, "X8"), t.SystemInt32Type), new MemoryOperand(input)) { NativeReadSize = 4 });
        if (shape == "i8-consumer") steps.Add(new(2, OpCode.Move, new LocalVariable("long", new(null, "X8"), t.SystemInt64Type), input));
        if (shape == "reference-consumer")
        {
            var target = new InjectedMethodAnalysisContext(t.SystemObjectType, "Reference", t.SystemVoidType,
                MethodAttributes.Public | MethodAttributes.Static, [t.SystemObjectType]);
            steps.Add(new(2, OpCode.CallVoid, target, input));
        }
        steps.Add(new(3, OpCode.Return, result));
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Read", resultType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = new(steps) };
        Assert.That(NativeScalarStorageRecovery.Recover(method), Is.EqualTo(expected ? 1 : 0));
        Assert.That(input.Type?.FullName, Is.EqualTo(expected ? "System.Int32" : null));
        Assert.That(operation.NativeArithmeticSize, Is.EqualTo(8), "Original X-register arithmetic width is not downgraded");
        Assert.That(operation.OpCode, Is.EqualTo(OpCode.And));
    }

    [TestCase(false, 4294967295L)]
    [TestCase(true, 4294967295L)]
    [TestCase(true, 2147483648L)]
    [TestCase(true, 255L)]
    public void ActualCilPreservesLow32BitsIncludingSignedInputsAndArrayNullFailure(bool scalar, long mask)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var array = new LocalVariable("input", new(null, "X19"), scalar ? t.SystemInt32Type : new SzArrayTypeAnalysisContext(t.SystemInt32Type));
        var length = new LocalVariable("length", new(null, "X22"));
        var result = new LocalVariable("result", new(null, "X20"), t.SystemInt32Type);
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Length", t.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        { ControlFlowGraph = new([new(0, OpCode.Move, length, scalar ? array : new ArrayLength(array)),
            new(1, OpCode.And, result, length, new Immediate(mask)) { NativeArithmeticSize = 8 }, new(2, OpCode.Return, result)]) };
        Assert.That(NativeScalarStorageRecovery.Recover(context), Is.EqualTo(1));
        var assembly = new AssemblyDefinition("MaskStorage" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("MaskStorage.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Fixture", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Length", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [scalar ? module.CorLibTypeFactory.Int32 : new SzArrayTypeSignature(module.CorLibTypeFactory.Int32)]));
        owner.Methods.Add(method); method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var locals = new Dictionary<LocalVariable, CilLocalVariable> {
            [array] = new(scalar ? module.CorLibTypeFactory.Int32 : new SzArrayTypeSignature(module.CorLibTypeFactory.Int32)),
            [length] = new(module.CorLibTypeFactory.Int32), [result] = new(module.CorLibTypeFactory.Int32) };
        foreach (var local in locals.Values) method.CilMethodBody.LocalVariables.Add(local);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0); method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, locals[array]);
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var operation in context.ControlFlowGraph.Instructions) emit.Invoke(null, [operation, context, method, locals, method]);
        using var stream = new MemoryStream(); module.Write(stream);
        var generated = Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Length")!;
        if (scalar)
            foreach (var value in new[] { 0, 1, -1, int.MinValue, int.MaxValue })
                Assert.That(generated.Invoke(null, [value]), Is.EqualTo(value & unchecked((int)mask)));
        else
        {
            foreach (var size in new[] { 0, 1, 31, 257 }) Assert.That(generated.Invoke(null, [new int[size]]), Is.EqualTo(size));
            var failure = Assert.Throws<TargetInvocationException>(() => generated.Invoke(null, [null]));
            Assert.That(failure!.InnerException, Is.TypeOf<NullReferenceException>());
        }
    }
}
