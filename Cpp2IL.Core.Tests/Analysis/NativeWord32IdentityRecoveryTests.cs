using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeWord32IdentityRecoveryTests
{
    [Test]
    public void NestedCancellationsAreProvenTogetherBeforeEitherRewrite()
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new(null, name), type);
        var input = Local("input", t.SystemUInt64Type); var offset = Local("offset");
        var middle = Local("middle"); var output = Local("output");
        var cfg = new ISILControlFlowGraph([]); var block = new Block { ID = 20 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, block];
        foreach (var b in cfg.Blocks) { b.Predecessors.Clear(); b.Successors.Clear(); }
        cfg.EntryBlock.Successors.Add(block); block.Predecessors.Add(cfg.EntryBlock);
        block.Successors.Add(cfg.ExitBlock); cfg.ExitBlock.Predecessors.Add(block);
        var subtract = new Instruction(0, OpCode.Subtract, offset, input, new Immediate(1)) { NativeArithmeticSize = 4 };
        var add = new Instruction(1, OpCode.Add, middle, offset, new Immediate(1)) { NativeArithmeticSize = 4 };
        var cancel = new Instruction(2, OpCode.Subtract, output, middle, new Immediate(1)) { NativeArithmeticSize = 4 };
        block.Instructions = [subtract, add, cancel, new(3, OpCode.Return, output)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemUInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = cfg,
            ParameterLocals = [input], Locals = [input, offset, middle, output] };
        foreach (var b in cfg.Blocks) b.CalculateBlockType();
        Assert.That(NativeWord32IdentityRecovery.RecoverAll(method), Is.EqualTo(2));
        Assert.That(add.OpCode, Is.EqualTo(OpCode.NumericConvert));
        Assert.That(add.Operands[3], Is.SameAs(input));
        Assert.That(cancel.OpCode, Is.EqualTo(OpCode.NumericConvert));
        Assert.That(cancel.Operands[3], Is.SameAs(offset));
        Assert.That(subtract.OpCode, Is.EqualTo(OpCode.Subtract));
        Assert.That(NativeWord32IdentityRecovery.RecoverAll(method), Is.Zero);
    }

    [TestCase("add-subtract", true)]
    [TestCase("subtract-add", true)]
    [TestCase("xor-xor", true)]
    [TestCase("wrap-constant", true)]
    [TestCase("negative-constant", true)]
    [TestCase("different-constants", false)]
    [TestCase("wide-inner", false)]
    [TestCase("wide-outer", false)]
    [TestCase("unknown-width", false)]
    [TestCase("floating-inner", false)]
    [TestCase("floating-outer", false)]
    [TestCase("same-operation", false)]
    [TestCase("outside-word-constant", false)]
    [TestCase("redefined-intermediate", false)]
    [TestCase("redefined-destination", false)]
    [TestCase("redefined-origin", false)]
    [TestCase("unanchored-origin", false)]
    [TestCase("reference-origin", false)]
    [TestCase("reference-intermediate", false)]
    [TestCase("reassigned-parameter", false)]
    [TestCase("reference-destination", false)]
    [TestCase("parameter-destination", false)]
    [TestCase("non-dominating-inner", false)]
    [TestCase("reverse-order", false)]
    public void OnlyExactWordIdentitiesAreReplacedWithUnsignedView(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new(null, name), type);
        var origin = Local("origin", t.SystemUInt64Type);
        var intermediate = Local("intermediate"); var destination = Local("destination");
        var cfg = new ISILControlFlowGraph([]); var block = new Block { ID = 20 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, block];
        foreach (var b in cfg.Blocks) { b.Predecessors.Clear(); b.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, block); Edge(block, cfg.ExitBlock);
        var constant = shape == "wrap-constant" ? uint.MaxValue : shape == "negative-constant" ? -1L : 1L;
        var inner = new Instruction(0, shape == "subtract-add" ? OpCode.Subtract : shape == "xor-xor" ? OpCode.Xor : OpCode.Add,
            intermediate, origin, new Immediate(constant)) { NativeArithmeticSize = 4 };
        var outer = new Instruction(1, shape == "subtract-add" ? OpCode.Add : shape == "xor-xor" ? OpCode.Xor : OpCode.Subtract,
            destination, intermediate, new Immediate(constant)) { NativeArithmeticSize = 4 };
        block.Instructions = [inner, outer, new(2, OpCode.Return, destination)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemUInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = cfg,
            ParameterLocals = [origin], Locals = [origin, intermediate, destination] };
        if (shape == "different-constants") outer.SetOperand(2, new Immediate(2));
        if (shape == "wide-inner") inner.NativeArithmeticSize = 8;
        if (shape == "wide-outer") outer.NativeArithmeticSize = 8;
        if (shape == "unknown-width") outer.NativeArithmeticSize = 0;
        if (shape == "floating-inner") inner.NativeFloatingPointSize = 4;
        if (shape == "floating-outer") outer.NativeFloatingPointSize = 4;
        if (shape == "same-operation") outer.OpCode = inner.OpCode;
        if (shape == "outside-word-constant") { inner.SetOperand(2, new Immediate(1L << 40)); outer.SetOperand(2, new Immediate(1L << 40)); }
        if (shape == "redefined-intermediate") block.Instructions.Insert(1, new(3, OpCode.Move, intermediate, origin));
        if (shape == "redefined-destination") block.Instructions.Insert(0, new(3, OpCode.Move, destination, origin));
        if (shape == "redefined-origin") {
            method.ParameterLocals = [];
            block.Instructions.Insert(0, new(3, OpCode.Move, origin, new Immediate(1)));
            block.Instructions.Insert(1, new(4, OpCode.Move, origin, new Immediate(2)));
        }
        if (shape == "unanchored-origin") method.ParameterLocals = [];
        if (shape == "reference-origin") origin.Type = t.SystemObjectType;
        if (shape == "reference-intermediate") intermediate.Type = t.SystemObjectType;
        if (shape == "reassigned-parameter") block.Instructions.Insert(0, new(3, OpCode.Move, origin, new Immediate(7)));
        if (shape == "reference-destination") destination.Type = t.SystemObjectType;
        if (shape == "parameter-destination") method.ParameterLocals.Add(destination);
        if (shape == "reverse-order") block.Instructions = [outer, inner, new(2, OpCode.Return, destination)];
        if (shape == "non-dominating-inner") {
            var bypass = new Block { ID = 21, Instructions = [new(4, OpCode.Jump, block)] };
            cfg.Blocks.Add(bypass); Edge(cfg.EntryBlock, bypass); Edge(bypass, block);
            block.Instructions.Remove(inner); bypass.Instructions.Insert(0, inner);
        }
        foreach (var b in cfg.Blocks) b.CalculateBlockType();
        var before = cfg.Instructions.Select(i => i.ToString()).ToArray();
        Assert.That(NativeWord32IdentityRecovery.TryRecover(method, outer), Is.EqualTo(expected));
        if (!expected) {
            Assert.That(cfg.Instructions.Select(i => i.ToString()).ToArray(), Is.EqualTo(before));
            return;
        }
        Assert.That(outer.OpCode, Is.EqualTo(OpCode.NumericConvert));
        Assert.That(outer.Operands[1], Is.SameAs(t.SystemUInt32Type));
        Assert.That(outer.Operands[2], Is.SameAs(t.SystemUInt64Type));
        Assert.That(outer.Operands[3], Is.SameAs(origin));
        Assert.That(outer.NativeIntegerSourceView, Is.True);
        Assert.That(inner.OpCode, Is.EqualTo(shape == "subtract-add" ? OpCode.Subtract : shape == "xor-xor" ? OpCode.Xor : OpCode.Add));
        foreach (var bits in new ulong[] { 0, 1, uint.MaxValue, 0x80000000, 0x100000000, ulong.MaxValue, 0xFEDCBA9876543210 }) {
            var word = unchecked((uint)bits); var c = unchecked((uint)constant);
            var actual = shape == "subtract-add" ? unchecked((word - c) + c)
                : shape == "xor-xor" ? (word ^ c) ^ c : unchecked((word + c) - c);
            Assert.That(actual, Is.EqualTo(word));
        }
    }
}
