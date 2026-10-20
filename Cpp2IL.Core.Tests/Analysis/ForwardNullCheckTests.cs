using System;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardNullCheckTests
{
    [Test]
    public void FullNullHelperFingerprintIsRequired()
    {
        var bytes = Convert.FromHexString("400000b4c0035fd6e00301aadd2d0114");
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes), Is.True);
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes[..^4]), Is.False);
        bytes[^1] ^= 1;
        Assert.That(ForwardNullCheckRecovery.MatchesHelperBytes(bytes), Is.False);
    }

    [TestCase("same", true)]
    [TestCase("copy", true)]
    [TestCase("linear-block", true)]
    [TestCase("different", false)]
    [TestCase("nonvirtual", false)]
    [TestCase("value-receiver", false)]
    [TestCase("overwrite", false)]
    [TestCase("call", false)]
    [TestCase("load", false)]
    [TestCase("store", false)]
    [TestCase("live-result", false)]
    [TestCase("branch", false)]
    public void NullThrowMustBePreservedByNextObservableCallOnSameValue(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var input = new LocalVariable("input", new Register(null, "input"), shape == "value-receiver" ? t.SystemInt32Type : t.SystemStringType);
        var alias = new LocalVariable("alias", new Register(null, "alias"), t.SystemStringType);
        var other = new LocalVariable("other", new Register(null, "other"), t.SystemStringType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var target = new InjectedMethodAnalysisContext(t.SystemObjectType, "Read", t.SystemVoidType, MethodAttributes.Public, []);
        var guard = new Instruction(0, OpCode.Call, new Immediate(0xa61e60), result, input);
        var call = new Instruction(10, OpCode.CallVoid, target, shape == "different" ? other : shape == "copy" ? alias : input)
            { NativeVirtualDispatch = shape != "nonvirtual" };
        var instructions = new List<Instruction> { guard };
        if (shape == "copy") instructions.Add(new(1, OpCode.Move, alias, input));
        if (shape == "overwrite") instructions.Add(new(1, OpCode.Move, input, other));
        if (shape == "call") instructions.Add(new(1, OpCode.CallVoid, new Immediate(123), input));
        if (shape == "load") instructions.Add(new(1, OpCode.Move, other, new MemoryOperand(input)));
        if (shape == "store") instructions.Add(new(1, OpCode.Move, new MemoryOperand(other), input));
        if (shape == "live-result") instructions.Add(new(1, OpCode.Move, other, result));
        if (shape == "branch") instructions.Add(new(1, OpCode.ConditionalJump, call, other));
        if (shape == "linear-block") instructions.Add(new(1, OpCode.Jump, call));
        instructions.Add(call); instructions.Add(new(11, OpCode.Return));
        var cfg = new ISILControlFlowGraph(instructions);
        Assert.That(ForwardNullCheckRecovery.FollowedBySameVirtualReceiver(cfg, guard), Is.EqualTo(expected));
        Assert.That(guard.OpCode, Is.EqualTo(OpCode.Call), "proof query must not mutate the graph");
    }
}
