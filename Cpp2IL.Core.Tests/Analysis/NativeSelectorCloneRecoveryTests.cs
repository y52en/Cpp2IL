using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeSelectorCloneRecoveryTests
{
    static byte[] Code(ulong address, ulong target, uint selector, bool boxed)
    {
        var words = new List<uint>();
        if (boxed) words.Add(0x91004000u);
        words.Add(selector == 0 ? 0x2a1f03e1u : 0x52800001u | (selector << 5));
        var pc = address + (ulong)words.Count * 4;
        words.Add(0x14000000u | ((uint)(((long)target - (long)pc) >> 2) & 0x03ffffffu));
        return words.SelectMany(BitConverter.GetBytes).ToArray();
    }

    [TestCase(0u, 0x12000UL)] [TestCase(2u, 0x12000UL)] [TestCase(3u, 0x12000UL)]
    [TestCase(0u, 0x8000UL)] [TestCase(2u, 0x8000UL)] [TestCase(65535u, 0x8000UL)]
    public void ExactOriginalSelectorAndAbsoluteBranchMatchAcrossDifferentEntryAddresses(uint selector, ulong target)
    {
        Assert.That(NativeSelectorCloneRecovery.TryKey(Code(0x10000, target, selector, true), 0x10000, true, out var wrapper), Is.True);
        Assert.That(NativeSelectorCloneRecovery.TryKey(Code(0x11000, target, selector, false), 0x11000, false, out var clone), Is.True);
        Assert.That(clone, Is.EqualTo(wrapper));
        Assert.That(clone.Selector, Is.EqualTo(selector)); Assert.That(clone.Target, Is.EqualTo(target));
    }

    [TestCase(0x320007e1u, 3u)] // Original Day: ORR W1,WZR,#3.
    [TestCase(0x321f03e1u, 2u)] // Original Month: ORR W1,WZR,#2.
    [TestCase(0x12800001u, uint.MaxValue)] // MOVN W1,#0.
    [TestCase(0x52a00021u, 65536u)] // MOVZ W1,#1,LSL #16.
    public void ActualSelectorEncodingsMatchTheSameSemanticWrapper(uint word, uint selector)
    {
        var bytes = Code(0x10000, 0x12000, 0, true);
        BitConverter.GetBytes(word).CopyTo(bytes, 4);
        Assert.That(NativeSelectorCloneRecovery.TryKey(bytes, 0x10000, true, out var key), Is.True);
        Assert.That(key, Is.EqualTo(new NativeSelectorCloneRecovery.Key(selector, 0x12000)));
    }

    [TestCase(0xb20003e1u)] // X1 is not the W1 selector contract.
    [TestCase(0x320003c1u)] // Input is W30, not WZR.
    [TestCase(0x320003e2u)] // Result is W2, not W1.
    [TestCase(0x324003e1u)] // N=1 is reserved for a 32-bit logical immediate.
    [TestCase(0x3200ffe1u)] // Reserved all-one immediate.
    [TestCase(0x3200fbe1u)] // Reserved element length zero.
    public void LogicalImmediateAliasesRequireTheExactW1ZeroSourceContract(uint word)
    {
        var bytes = Code(0x10000, 0x12000, 0, true);
        BitConverter.GetBytes(word).CopyTo(bytes, 4);
        Assert.That(NativeSelectorCloneRecovery.TryKey(bytes, 0x10000, true, out _), Is.False);
    }

    [Test]
    public void AllValidLogicalImmediateFieldsMatchIndependentRotatedBitStrings()
    {
        var tested = 0;
        for (var length = 1; length <= 5; length++)
        {
            var size = 1 << length;
            for (var ones = 1; ones < size; ones++)
            for (var rotation = 0; rotation < 64; rotation++)
            {
                // Build the architectural low-bit element as a string, rotate
                // right, and replicate. No integer decoder operations reused.
                var element = new string('0', size - ones) + new string('1', ones);
                var right = rotation % size;
                if (right != 0) element = element[^right..] + element[..^right];
                var expected = Convert.ToUInt32(string.Concat(Enumerable.Repeat(element, 32 / size)), 2);
                var imms = ((~(size - 1) << 1) | (ones - 1)) & 63;
                var word = 0x320003e1u | ((uint)rotation << 16) | ((uint)imms << 10);
                var bytes = Code(0x10000, 0x12000, 0, false);
                BitConverter.GetBytes(word).CopyTo(bytes, 0);
                Assert.That(NativeSelectorCloneRecovery.TryKey(bytes, 0x10000, false, out var key), Is.True);
                Assert.That(key.Selector, Is.EqualTo(expected), $"word={word:X8}"); tested++;
            }
        }
        Assert.That(tested, Is.EqualTo(3648));
    }

    [TestCase("wrong-header")] [TestCase("wrong-receiver")] [TestCase("wrong-selector-register")]
    [TestCase("branch-with-link")] [TestCase("conditional")] [TestCase("short")]
    [TestCase("misaligned")] [TestCase("self-loop")]
    public void SimilarOrIncompleteCodeNeverAuthenticatesASelectorAlias(string shape)
    {
        var bytes = Code(0x10000, shape == "self-loop" ? 0x10004UL : 0x12000UL, 3, true);
        if (shape == "wrong-header") BitConverter.GetBytes(0x91008000u).CopyTo(bytes, 0);
        if (shape == "wrong-receiver") BitConverter.GetBytes(0x91004020u).CopyTo(bytes, 0);
        if (shape == "wrong-selector-register") BitConverter.GetBytes(0x52800062u).CopyTo(bytes, 4);
        if (shape == "branch-with-link") bytes[11] |= 0x80;
        if (shape == "conditional") BitConverter.GetBytes(0x54000000u).CopyTo(bytes, 8);
        if (shape == "short") bytes = bytes[..8];
        Assert.That(NativeSelectorCloneRecovery.TryKey(bytes, shape == "misaligned" ? 0x10001UL : 0x10000UL, true, out _), Is.False);
    }

    [Test]
    public void SelectorOrDestinationDifferencesAreNotDiscardedLikeStructuralNameCandidates()
    {
        NativeSelectorCloneRecovery.TryKey(Code(0x10000, 0x12000, 3, true), 0x10000, true, out var expected);
        NativeSelectorCloneRecovery.TryKey(Code(0x11000, 0x12004, 3, false), 0x11000, false, out var otherTarget);
        NativeSelectorCloneRecovery.TryKey(Code(0x11000, 0x12000, 2, false), 0x11000, false, out var otherSelector);
        Assert.That(otherTarget, Is.Not.EqualTo(expected)); Assert.That(otherSelector, Is.Not.EqualTo(expected));
    }

    [TestCase("address")] [TestCase("byref")] [TestCase("padding")]
    [TestCase("different-owner")] [TestCase("byvalue")]
    [TestCase("known-wrong-result")] [TestCase("ambiguous")]
    [TestCase("unreviewed")] [TestCase("virtual")]
    [TestCase("effectful-padding")] [TestCase("wrong-native-target")]
    public void OnlyExactMetadataBoundByrefReceiverAndSingleOriginalMethodCanBind(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var date = types.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.DateTime")!;
        var target = date.Methods.Single(m => m.Name == "get_Year");
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var input = new LocalVariable("date", new Register(null, "date"), shape == "different-owner" ? types.SystemInt64Type : date);
        var reference = new LocalVariable("reference", new Register(null, "reference"), new ByRefTypeAnalysisContext(date));
        var result = new LocalVariable("result", new Register(null, "result"), shape == "known-wrong-result" ? types.SystemStringType : null);
        IOperand receiver = shape == "byref" ? reference : shape == "byvalue" ? input : new AddressOf(input);
        var call = new Instruction(2, OpCode.Call, new Immediate(0x10000), result, receiver, new Immediate(0))
            {NativeDirectCallTarget = shape == "wrong-native-target" ? 0x10004UL : 0x10000UL,
                NativeVirtualDispatch = shape == "virtual"};
        if (shape == "padding") call.AddOperands([input, new Immediate(12)]);
        if (shape == "effectful-padding") call.AddOperands([new MemoryOperand(input, addend: 4)]);
        var before = new Instruction(1, OpCode.CallVoid, new StringLiteral("before"));
        var after = new Instruction(3, OpCode.CallVoid, new StringLiteral("after"));
        caller.ControlFlowGraph = new([before, call, after, new(4, OpCode.Return, result)]);
        caller.Locals.AddRange([input, reference, result]);
        var nodes = caller.ControlFlowGraph.Instructions.ToArray(); var operands = call.Operands.ToArray();
        var candidates = shape == "ambiguous" ? new[] {target, date.Methods.Single(m => m.Name == "get_Month")} : [target];
        var accepted = shape is "address" or "byref" or "padding";
        Assert.That(NativeSelectorCloneRecovery.TryRewrite(caller, call, candidates, shape != "unreviewed"), Is.EqualTo(accepted));
        Assert.That(caller.ControlFlowGraph.Instructions.ToArray(), Is.EqualTo(nodes));
        Assert.That(call.NativeDirectCallTarget, Is.EqualTo(shape == "wrong-native-target" ? 0x10004UL : 0x10000UL));
        if (accepted)
        {
            Assert.That(call.Operands.ToArray(), Is.EqualTo(new IOperand[] {target, result, receiver}));
            Assert.That(result.Type, Is.SameAs(types.SystemInt32Type));
        }
        else
        {
            Assert.That(call.Operands.ToArray(), Is.EqualTo(operands));
            Assert.That(result.Type, Is.SameAs(shape == "known-wrong-result" ? types.SystemStringType : null));
        }
    }

    [TestCase("single")] [TestCase("double")] [TestCase("aggregate")]
    public void IntegerCallSnapshotNeverBecomesAFloatingOrAggregateReturn(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var date = types.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.DateTime")!;
        var returned = shape == "single" ? types.SystemSingleType : shape == "double" ? types.SystemDoubleType : date;
        var target = new InjectedMethodAnalysisContext(date, "UnsupportedReturn", returned, MethodAttributes.Public, []);
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var input = new LocalVariable("date", new Register(null, "date"), date);
        var result = new LocalVariable("result", new Register(null, "X0"));
        var call = new Instruction(0, OpCode.Call, new Immediate(0x10000), result, new AddressOf(input))
            {NativeDirectCallTarget = 0x10000};
        caller.ControlFlowGraph = new([call, new(1, OpCode.Return)]); caller.Locals.AddRange([input, result]);
        Assert.That(NativeSelectorCloneRecovery.TryRewrite(caller, call, [target], true), Is.False);
        Assert.That(call.Operands[0], Is.TypeOf<Immediate>()); Assert.That(result.Type, Is.Null);
    }

    [Test]
    public void ProductionDoesNotApplyOriginalImageAliasesToAForeignFixture()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Foreign",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new([new(0, OpCode.Return)]);
        Assert.That(NativeSelectorCloneRecovery.Run(method), Is.Zero);
    }
}
