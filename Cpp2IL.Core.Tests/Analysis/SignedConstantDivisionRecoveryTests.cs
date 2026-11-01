using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SignedConstantDivisionRecoveryTests
{
    [TestCase(-2004318071, 5, true, 60)]
    [TestCase(-2004318071, 6, true, 120)]
    [TestCase(-1851608123, 11, true, 3600)]
    [TestCase(-1037155065, 16, true, 86400)]
    [TestCase(0x66666667, 2, false, 10)]
    [TestCase(0x55555556, 0, false, 3)]
    public void ExactQuotientIntervalBoundsProveTheWholeSignedWordDomain(int magic, int shift, bool add, int expected)
    {
        Assert.That(SignedConstantDivisionRecovery.ProveDivisor(magic, shift, add, out var divisor), Is.True);
        Assert.That(divisor, Is.EqualTo(expected));
    }

    [TestCase(0, 0, false)] [TestCase(1, -1, false)] [TestCase(1, 32, false)]
    [TestCase(-2004318071, 5, false)] [TestCase(0x55555556, 0, true)]
    [TestCase(0x40000000, 0, false)] [TestCase(0x55555557, 0, false)]
    [TestCase(-2004318071, 0, true)]
    public void ApproximateOrIncorrectMagicIsNeverAProof(int magic, int shift, bool add)
        => Assert.That(SignedConstantDivisionRecovery.ProveDivisor(magic, shift, add, out _), Is.False);

    static (MethodAnalysisContext Method, Instruction Root, LocalVariable Input, Instruction Product, Instruction High,
        Instruction Adjust, Instruction Arithmetic, Instruction Sign, LocalVariable Result) Fixture(int magic, int shift, bool add, bool unsignedResult = false)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        LocalVariable L(string name, TypeAnalysisContext type) => new(name, new(null, name), type);
        var input = L("input", t.SystemInt32Type); var product = L("product", t.SystemInt64Type);
        var bits = L("bits", t.SystemUInt64Type); var high = L("high", t.SystemUInt64Type);
        var adjusted = L("adjusted", t.SystemUInt32Type); var signed = L("signed", t.SystemInt32Type);
        var quotient = L("quotient", t.SystemInt32Type); var signInput = L("signInput", t.SystemUInt32Type);
        var correction = L("correction", t.SystemUInt32Type);
        var result = L("result", unsignedResult ? t.SystemUInt32Type : t.SystemInt32Type);
        var multiply = new Instruction(0, OpCode.Multiply, product, input, new Immediate(magic))
            { NativeArithmeticSize = 8, NativeMultiplyInputSize = 4, NativeMultiplySigned = true };
        var wide = new Instruction(1, OpCode.NumericConvert, bits, t.SystemUInt64Type, t.SystemInt64Type, product)
            { NativeArithmeticSize = 8 };
        var extract = new Instruction(2, OpCode.ShiftRightUnsigned, high, bits, new Immediate(32)) { NativeArithmeticSize = 8 };
        var adjust = new Instruction(3, OpCode.Add, adjusted, high, input) { NativeArithmeticSize = 4 };
        IOperand middle = add ? adjusted : high;
        var arithmetic = new Instruction(5, OpCode.ShiftRight, quotient, signed, new Immediate(shift)) { NativeArithmeticSize = 4 };
        var sign = new Instruction(7, OpCode.ShiftRightUnsigned, correction, signInput, new Immediate(31)) { NativeArithmeticSize = 4 };
        var root = new Instruction(8, OpCode.Add, result, quotient, correction) { NativeArithmeticSize = 4 };
        var instructions = new List<Instruction> { multiply, wide, extract };
        if (add) instructions.Add(adjust);
        instructions.AddRange([
            new(4, OpCode.NumericConvert, signed, t.SystemInt32Type, t.SystemUInt32Type, middle)
                { NativeArithmeticSize = 4, NativeIntegerSourceView = true }, arithmetic,
            new(6, OpCode.NumericConvert, signInput, t.SystemUInt32Type, t.SystemUInt32Type, middle)
                { NativeArithmeticSize = 4, NativeIntegerSourceView = true }, sign, root,
            new(9, OpCode.Return, result)]);
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Calculate", t.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, [t.SystemInt32Type])
            { ControlFlowGraph = new(instructions), ParameterLocals = [input],
                Locals = [input, product, bits, high, adjusted, signed, quotient, signInput, correction, result] };
        return (context, root, input, multiply, extract, adjust, arithmetic, sign, result);
    }

    [TestCase("valid", true)] [TestCase("effects", true)] [TestCase("shared-product", true)]
    [TestCase("unsigned-multiply", false)] [TestCase("wide-input", false)] [TestCase("narrow-product", false)]
    [TestCase("wrong-high-shift", false)] [TestCase("wrong-sign-shift", false)] [TestCase("logical-quotient", false)]
    [TestCase("wrong-sign-source", false)] [TestCase("unknown-input", false)] [TestCase("long-input", true)]
    [TestCase("address-taken", false)] [TestCase("two-writes", false)] [TestCase("duplicate-intermediate", false)]
    [TestCase("unbound-input", false)] [TestCase("wide-result", false)]
    [TestCase("wide-convert-truncation", false)] [TestCase("wide-move-truncation", false)] [TestCase("non-dominating", false)]
    public void RewriteRequiresCompleteNativeWidthsStableSsaAndDominance(string shape, bool expected)
    {
        var f = Fixture(-2004318071, 5, true); var method = f.Method; var t = method.AppContext.SystemTypes;
        var cfg = method.ControlFlowGraph!; var home = cfg.Blocks.Single(b => b.Instructions.Contains(f.Root));
        if (shape == "unsigned-multiply") f.Product.NativeMultiplySigned = false;
        if (shape == "wide-input") f.Product.NativeMultiplyInputSize = 8;
        if (shape == "narrow-product") f.Product.NativeArithmeticSize = 4;
        if (shape == "wrong-high-shift") f.High.SetOperand(2, new Immediate(31));
        if (shape == "wrong-sign-shift") f.Sign.SetOperand(2, new Immediate(30));
        if (shape == "logical-quotient") f.Arithmetic.OpCode = OpCode.ShiftRightUnsigned;
        if (shape == "wrong-sign-source") f.Sign.SetOperand(1, f.Input);
        if (shape == "unknown-input") f.Input.Type = null;
        if (shape == "long-input") f.Input.Type = t.SystemInt64Type;
        if (shape == "unbound-input") { method.ParameterLocals.Clear(); method.Locals.Remove(f.Input); }
        if (shape == "wide-result") f.Result.Type = t.SystemInt64Type;
        if (shape == "duplicate-intermediate") home.Instructions.Insert(4, new(20, OpCode.Move, f.Adjust.Operands[0], new Immediate(2)));
        if (shape == "two-writes") home.Instructions.InsertRange(0,
            [new(20, OpCode.Move, f.Input, new Immediate(1)), new(21, OpCode.Move, f.Input, new Immediate(2))]);
        if (shape == "address-taken") home.Instructions.Insert(0, new(20, OpCode.CallVoid, new StringLiteral("alias"), new AddressOf(f.Input)));
        if (shape is "wide-convert-truncation" or "wide-move-truncation")
        {
            var truncated = new LocalVariable("truncated", new(null, "truncated"), shape == "wide-convert-truncation" ? t.SystemUInt32Type : t.SystemUInt64Type);
            method.Locals.Add(truncated);
            home.Instructions.Insert(2, shape == "wide-convert-truncation"
                ? new(20, OpCode.NumericConvert, truncated, t.SystemUInt32Type, t.SystemUInt32Type, f.Product.Operands[0]) { NativeArithmeticSize = 4 }
                : new(20, OpCode.Move, truncated, f.Product.Operands[0]) { NativeRegisterCopySize = 4 });
            f.High.SetOperand(1, truncated);
        }
        if (shape == "effects") home.Instructions.Insert(home.Instructions.IndexOf(f.Root), new(20, OpCode.CallVoid, new StringLiteral("effect")));
        if (shape == "shared-product") home.Instructions.Insert(home.Instructions.IndexOf(f.Root), new(20, OpCode.CallVoid, new StringLiteral("observe"), f.Product.Operands[0]));
        if (shape == "non-dominating")
        {
            var prefix = new Block { ID = 100, Instructions = home.Instructions.Take(home.Instructions.IndexOf(f.Root)).ToList() };
            home.Instructions = [f.Root, home.Instructions.Last()]; cfg.Blocks.Add(prefix);
            cfg.EntryBlock.Successors.Add(prefix); prefix.Predecessors.Add(cfg.EntryBlock);
            prefix.Successors.Add(home); home.Predecessors.Add(prefix);
        }
        var nodes = cfg.Instructions.ToArray(); var calls = nodes.Where(i => i.OpCode == OpCode.CallVoid).ToArray();
        var inputType = f.Input.Type;
        Assert.That(SignedConstantDivisionRecovery.Rewrite(method, f.Root), Is.EqualTo(expected));
        Assert.That(f.Input.Type, Is.SameAs(inputType));
        Assert.That(cfg.Instructions.Where(i => i.OpCode == OpCode.CallVoid), Is.EqualTo(calls));
        if (!expected) { Assert.That(cfg.Instructions, Is.EqualTo(nodes)); return; }
        Assert.That(f.Root.OpCode, Is.EqualTo(OpCode.NumericConvert));
        var divide = cfg.Instructions.Single(i => i.OpCode == OpCode.Divide);
        Assert.That(((Immediate)divide.Operands[2]).Value, Is.EqualTo(60));
        Assert.That(((LocalVariable)divide.Operands[1]).Type, Is.SameAs(t.SystemInt32Type));
        Assert.That(cfg.Instructions, Does.Contain(f.Product)); // Shared intermediate is never erased by Rewrite.
    }

    static Delegate Executable(MethodAnalysisContext context, bool wideInput = false)
    {
        var assembly = new AssemblyDefinition("Division" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("Division.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0))); assembly.Modules.Add(module);
        var owner = new TypeDefinition("Fixture", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var generated = new MethodDefinition("Calculate", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [wideInput ? module.CorLibTypeFactory.Int64 : module.CorLibTypeFactory.Int32]));
        generated.CilMethodBody = new CilMethodBody { InitializeLocals = true }; owner.Methods.Add(generated);
        TypeSignature Signature(TypeAnalysisContext type) => type.FullName switch
        {
            "System.Int32" => module.CorLibTypeFactory.Int32, "System.UInt32" => module.CorLibTypeFactory.UInt32,
            "System.Int64" => module.CorLibTypeFactory.Int64, "System.UInt64" => module.CorLibTypeFactory.UInt64,
            _ => throw new InvalidOperationException(type.FullName),
        };
        var locals = context.Locals.ToDictionary(v => v, v => new CilLocalVariable(Signature(v.Type!)));
        foreach (var l in locals.Values) generated.CilMethodBody.LocalVariables.Add(l);
        generated.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0); generated.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, locals[context.ParameterLocals[0]]);
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var i in context.ControlFlowGraph!.Instructions.Where(i => i.OpCode is not (OpCode.Nop or OpCode.Jump))) emit.Invoke(null, [i, context, generated, locals, generated]);
        using var stream = new MemoryStream(); module.Write(stream);
        return Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Calculate")!.CreateDelegate(wideInput ? typeof(Func<long, int>) : typeof(Func<int, int>));
    }

    [TestCase(-2004318071, 5, true, 60, false)] [TestCase(-2004318071, 5, true, 60, true)]
    [TestCase(-1851608123, 11, true, 3600, false)] [TestCase(-1851608123, 11, true, 3600, true)]
    [TestCase(-1037155065, 16, true, 86400, false)] [TestCase(-1037155065, 16, true, 86400, true)]
    [TestCase(0x66666667, 2, false, 10, false)] [TestCase(0x66666667, 2, false, 10, true)]
    [TestCase(0x55555556, 0, false, 3, false)] [TestCase(0x55555556, 0, false, 3, true)]
    public void ActualOriginalAndRewrittenCilMatchDivisionIncludingMinValue(int magic, int shift, bool add, int divisor, bool unsigned)
    {
        var f = Fixture(magic, shift, add, unsigned); var before = (Func<int, int>)Executable(f.Method);
        Assert.That(SignedConstantDivisionRecovery.Rewrite(f.Method, f.Root), Is.True);
        var after = (Func<int, int>)Executable(f.Method);
        var values = new List<int> { int.MinValue, int.MinValue + 1, -divisor - 1, -divisor, -divisor + 1, -1, 0, 1, divisor - 1, divisor, divisor + 1, int.MaxValue - 1, int.MaxValue };
        var random = new Random(38911); for (var i = 0; i < 1000; i++) values.Add((int)random.NextInt64(int.MinValue, (long)int.MaxValue + 1));
        foreach (var n in values)
        { Assert.That(before(n), Is.EqualTo(n / divisor), $"native-lowered n={n}"); Assert.That(after(n), Is.EqualTo(n / divisor), $"recovered n={n}"); }
    }

    [TestCase(false)] [TestCase(true)]
    public void ActualWideManagedCarrierUsesOnlyTheSignedNativeLowWord(bool unsignedResult)
    {
        var f = Fixture(-2004318071, 5, true, unsignedResult);
        f.Input.Type = f.Method.AppContext.SystemTypes.SystemInt64Type;
        var before = (Func<long, int>)Executable(f.Method, true);
        Assert.That(SignedConstantDivisionRecovery.Rewrite(f.Method, f.Root), Is.True);
        var after = (Func<long, int>)Executable(f.Method, true);
        var values = new List<long> { long.MinValue, long.MinValue + 1, long.MaxValue, 0, 60, 1L << 32,
            (1L << 32) + 60, -(1L << 32) - 60, 0x1234567880000000L, 0x00000000ffffffffL, -1, int.MinValue, int.MaxValue };
        var random = new Random(38912);
        for (var i = 0; i < 1000; i++) values.Add(i % 2 == 0 ? random.NextInt64() : -random.NextInt64());
        foreach (var n in values)
        {
            var expected = unchecked((int)n) / 60;
            Assert.That(before(n), Is.EqualTo(expected), $"native low word n={n}");
            Assert.That(after(n), Is.EqualTo(expected), $"recovered low word n={n}");
        }
    }
}
