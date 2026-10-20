using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PhiMemoryLoadRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("addend", true)]
    [TestCase("fallthrough", true)]
    [TestCase("object-field-address", true)]
    [TestCase("runtime-address-not-flattened", true)]
    [TestCase("callback-in-join", false)]
    [TestCase("write-in-join", false)]
    [TestCase("critical-edge", false)]
    [TestCase("unknown-width", false)]
    [TestCase("indexed-load", false)]
    [TestCase("pointer-escape", false)]
    [TestCase("pointer-nested-escape", false)]
    [TestCase("self-phi", false)]
    [TestCase("constant-input", false)]
    [TestCase("missing-input", false)]
    [TestCase("undefined-input", false)]
    [TestCase("multiple-value-definitions", false)]
    [TestCase("non-dominating-input", false)]
    public void ReadMovesOnlyOntoUnconditionalIncomingEdges(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        LocalVariable Local(string n) => new(n, new(null, n));
        var left = Local("left"); var right = Local("right"); var pointer = Local("pointer");
        var value = new LocalVariable("value", new(null, "value"), t.SystemStringType);
        var flag = new LocalVariable("flag", new(null, "flag"), t.SystemBooleanType);
        var root = new LocalVariable("root", new(null, "root"), shape == "runtime-address-not-flattened"
            ? new StaticFieldStorageTypeAnalysisContext(t.SystemStringType, t.SystemStringType.DeclaringAssembly) : t.SystemObjectType);
        var cfg = new ISILControlFlowGraph([]);
        var branch = new Block { ID = 20 }; var a = new Block { ID = 21 }; var b = new Block { ID = 22 }; var join = new Block { ID = 23 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, branch, a, b, join];
        foreach (var block in cfg.Blocks) { block.Predecessors.Clear(); block.Successors.Clear(); }
        void Edge(Block x, Block y) { x.Successors.Add(y); y.Predecessors.Add(x); }
        Edge(cfg.EntryBlock, branch); Edge(branch, a); Edge(branch, b); Edge(a, join); Edge(b, join); Edge(join, cfg.ExitBlock);
        branch.Instructions = [new(0, OpCode.ConditionalJump, a, flag)];
        a.Instructions = [new(1, OpCode.Jump, join)]; b.Instructions = [new(2, OpCode.Jump, join)];
        var phi = new Instruction(-1, OpCode.Phi, pointer, left, right);
        var load = new Instruction(3, OpCode.Move, value, new MemoryOperand(pointer, addend: shape == "addend" ? 16 : 0)) { NativeReadSize = 8 };
        join.Instructions = [phi, load, new(4, OpCode.Return, value)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemStringType, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [left, right, flag], Locals = [left, right, flag, pointer, value] };
        if (shape == "fallthrough") b.Instructions.Clear();
        if (shape is "object-field-address" or "runtime-address-not-flattened")
        {
            method.ParameterLocals = [root, right, flag]; method.Locals.Add(root);
            a.Instructions.Insert(0, new(5, OpCode.Add, left, root, new Immediate(32)));
        }
        if (shape == "callback-in-join") join.Instructions.Insert(1, new(5, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "write-in-join") join.Instructions.Insert(1, new(5, OpCode.Move, new MemoryOperand(left), right));
        if (shape == "critical-edge") Edge(a, cfg.ExitBlock);
        if (shape == "unknown-width") load.NativeReadSize = 0;
        if (shape == "indexed-load") load.SetOperand(1, new MemoryOperand(pointer, left, 0, 8));
        if (shape == "pointer-escape") join.Instructions.Add(new(5, OpCode.CallVoid, new StringLiteral("observe"), pointer));
        if (shape == "pointer-nested-escape") join.Instructions.Add(new(5, OpCode.Move, right, new AddressOf(pointer)));
        if (shape == "self-phi") phi.SetOperand(2, pointer);
        if (shape == "constant-input") phi.SetOperand(2, new Immediate(0));
        if (shape == "missing-input") phi.RemoveOperandAt(2);
        if (shape == "undefined-input") method.ParameterLocals = [left, flag];
        if (shape == "multiple-value-definitions") a.Instructions.Insert(0, new(5, OpCode.Move, value, new Immediate(0)));
        if (shape == "non-dominating-input") { method.ParameterLocals = [left, flag]; a.Instructions.Insert(0, new(5, OpCode.Move, right, left)); }
        foreach (var block in cfg.Blocks) block.CalculateBlockType();
        var original = cfg.Instructions.ToArray();
        Assert.That(PhiMemoryLoadRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        if (!expected) Assert.That(cfg.Instructions, Is.EqualTo(original));
        else
        {
            Assert.That(phi.Operands[0], Is.SameAs(value));
            Assert.That(join.Instructions.Contains(load), Is.False);
            foreach (var block in new[] { a, b })
            {
                var read = block.Instructions.Single(i => i.OpCode == OpCode.Move);
                Assert.That(read.NativeReadSize, Is.EqualTo(8));
                var flattened = shape == "object-field-address" && ReferenceEquals(block, a);
                Assert.That(((MemoryOperand)read.Operands[1]).Base, Is.SameAs(flattened ? root : ReferenceEquals(block, a) ? left : right));
                Assert.That(((MemoryOperand)read.Operands[1]).Addend, Is.EqualTo(flattened ? 32 : shape == "addend" ? 16 : 0));
            }
        }
    }
}
