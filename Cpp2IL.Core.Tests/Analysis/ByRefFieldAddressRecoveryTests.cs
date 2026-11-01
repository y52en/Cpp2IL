using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ByRefFieldAddressRecoveryTests
{
    [TestCase("read", true)]
    [TestCase("store", true)]
    [TestCase("addend", true)]
    [TestCase("partial", false)]
    [TestCase("padding", false)]
    [TestCase("overlap", false)]
    [TestCase("narrow-address", false)]
    [TestCase("unknown-width", false)]
    [TestCase("reference-root", false)]
    [TestCase("raw-pointer", false)]
    [TestCase("value-copy", false)]
    [TestCase("root-reassigned", false)]
    [TestCase("address-reassigned", false)]
    public void OnlyCompleteMetadataProvenFieldsOfStableManagedReferencesAreRecovered(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var data = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Data",
            t.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.SequentialLayout);
        var field = new InjectedFieldAnalysisContext("Tag", t.SystemInt32Type, FieldAttributes.Public, data, 12);
        data.Fields.Add(field);
        if (shape == "overlap") data.Fields.Add(new InjectedFieldAnalysisContext("Alias", t.SystemInt32Type, FieldAttributes.Public, data, 12));
        TypeAnalysisContext rootType = new ByRefTypeAnalysisContext(data);
        if (shape == "reference-root") rootType = new ByRefTypeAnalysisContext(t.SystemObjectType);
        if (shape == "raw-pointer") rootType = data.MakePointerType();
        if (shape == "value-copy") rootType = data;
        var root = new LocalVariable("root", new(null, "root"), rootType);
        var pointer = new LocalVariable("pointer", new(null, "pointer"));
        var value = new LocalVariable("value", new(null, "value"), t.SystemInt32Type);
        var address = new Instruction(0, OpCode.Add, pointer, root, new Immediate(shape is "addend" or "padding" ? 8 : 12))
            { NativeArithmeticSize = shape == "narrow-address" ? 4 : 8 };
        var memory = new MemoryOperand(pointer, addend: shape == "addend" ? 4 : 0);
        var access = shape == "store" ? new Instruction(1, OpCode.Move, memory, value) { NativeWriteSize = 4 }
            : new Instruction(1, OpCode.Move, value, memory) { NativeReadSize = shape == "unknown-width" ? 0 : shape == "partial" ? 2 : 4 };
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Run", t.SystemInt32Type, MethodAttributes.Public | MethodAttributes.Static, [])
        { ParameterLocals = [root], Locals = [root, pointer, value], ControlFlowGraph = new([address, access, new(2, OpCode.Return, value)]) };
        if (shape == "root-reassigned") method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(address)).Instructions.Insert(1,
            new(3, OpCode.Move, root, new Immediate(0)));
        if (shape == "address-reassigned") method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(address)).Instructions.Insert(1,
            new(3, OpCode.Move, pointer, new Immediate(0)));
        var index = shape == "store" ? 0 : 1;
        var originalOperand = access.Operands[index];
        Assert.That(SsaFieldAddressRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        if (expected)
        {
            Assert.That(access.Operands[index], Is.TypeOf<FieldReference>());
            var recovered = (FieldReference)access.Operands[index];
            Assert.That(recovered.Field, Is.SameAs(field));
            Assert.That(recovered.Local, Is.SameAs(root));
            Assert.That(recovered.Offset, Is.EqualTo(12));
        }
        else Assert.That(access.Operands[index], Is.SameAs(originalOperand));
    }

    [Test]
    public void SelectedPointerLoadsKeepTheirOriginalEdgesAndFieldIdentities()
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var data = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Schedule",
            t.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.SequentialLayout);
        var self = new InjectedFieldAnalysisContext("Self", t.SystemInt32Type, FieldAttributes.Public, data, 8);
        var other = new InjectedFieldAnalysisContext("Other", t.SystemInt32Type, FieldAttributes.Public, data, 12);
        data.Fields.Add(self); data.Fields.Add(other);
        var root = new LocalVariable("pseg", new(null, "pseg"), new ByRefTypeAnalysisContext(data));
        var left = new LocalVariable("left", new(null, "left"));
        var right = new LocalVariable("right", new(null, "right"));
        var pointer = new LocalVariable("pointer", new(null, "pointer"));
        var value = new LocalVariable("tag", new(null, "tag"), t.SystemInt32Type);
        var flag = new LocalVariable("flag", new(null, "flag"), t.SystemBooleanType);
        var cfg = new ISILControlFlowGraph([]);
        var branch = new Block { ID = 20 }; var a = new Block { ID = 21 }; var b = new Block { ID = 22 }; var join = new Block { ID = 23 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, branch, a, b, join];
        foreach (var block in cfg.Blocks) { block.Predecessors.Clear(); block.Successors.Clear(); }
        void Edge(Block x, Block y) { x.Successors.Add(y); y.Predecessors.Add(x); }
        Edge(cfg.EntryBlock, branch); Edge(branch, a); Edge(branch, b); Edge(a, join); Edge(b, join); Edge(join, cfg.ExitBlock);
        branch.Instructions = [new(0, OpCode.Add, left, root, new Immediate(8)) { NativeArithmeticSize = 8 },
            new(1, OpCode.Add, right, root, new Immediate(12)) { NativeArithmeticSize = 8 }, new(2, OpCode.ConditionalJump, a, flag)];
        a.Instructions = [new(3, OpCode.Jump, join)]; b.Instructions = [new(4, OpCode.Jump, join)];
        join.Instructions = [new(-1, OpCode.Phi, pointer, left, right),
            new(5, OpCode.Move, value, new MemoryOperand(pointer)) { NativeReadSize = 4 }, new(6, OpCode.Return, value)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Choose", t.SystemInt32Type, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [root, flag], Locals = [root, flag, left, right, pointer, value] };
        foreach (var block in cfg.Blocks) block.CalculateBlockType();
        Assert.That(PhiMemoryLoadRecovery.Run(method), Is.EqualTo(1));
        var original = cfg.Blocks.ToDictionary(x => x, x => x.Instructions.ToArray());
        Assert.That(SsaFieldAddressRecovery.Run(method), Is.EqualTo(2));
        foreach (var block in cfg.Blocks) Assert.That(block.Instructions, Is.EqualTo(original[block]), "No load may be moved or inserted");
        Assert.That(((FieldReference)a.Instructions.Single(i => i.OpCode == OpCode.Move).Operands[1]).Field, Is.SameAs(self));
        Assert.That(((FieldReference)b.Instructions.Single(i => i.OpCode == OpCode.Move).Operands[1]).Field, Is.SameAs(other));
        Assert.That(a.Instructions.Single(i => i.OpCode == OpCode.Move).NativeReadSize, Is.EqualTo(4));
        Assert.That(b.Instructions.Single(i => i.OpCode == OpCode.Move).NativeReadSize, Is.EqualTo(4));
    }
}
