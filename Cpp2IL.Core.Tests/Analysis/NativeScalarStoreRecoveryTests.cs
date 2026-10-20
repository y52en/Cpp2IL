using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeScalarStoreRecoveryTests
{
    [Test]
    public void ReceiverOverwriteProofRequiresBothCompleteBodies()
    {
        var caller = Convert.FromHexString("FF8300D1FD7B01A9FD430091FF7F00A9AE230094E1CE00B082C400F021C0079142381991E3030091EDFEFF97FD7B41A9FF830091C0035FD6");
        var getter = Convert.FromHexString("682301B0089143F9000140F9C0035FD6");
        Assert.That(NativeScalarStoreRecovery.MatchesReceiverOverwriteBodies(caller, getter), Is.True);
        Assert.That(NativeScalarStoreRecovery.MatchesReceiverOverwriteBodies(caller[..52], getter), Is.False);
        caller[0] ^= 1;
        Assert.That(NativeScalarStoreRecovery.MatchesReceiverOverwriteBodies(caller, getter), Is.False);
        caller[0] ^= 1; getter[8] ^= 1;
        Assert.That(NativeScalarStoreRecovery.MatchesReceiverOverwriteBodies(caller, getter), Is.False);
    }

    [Test]
    public void FingerprintRequiresTheCompleteInspectedBody()
    {
        var bytes = Convert.FromHexString("0004002D020800BDC0035FD6");
        Assert.That(NativeScalarStoreRecovery.MatchesBody(bytes), Is.True);
        Assert.That(NativeScalarStoreRecovery.MatchesBody(bytes[..8]), Is.False);
        bytes[0] ^= 1;
        Assert.That(NativeScalarStoreRecovery.MatchesBody(bytes), Is.False);
        Assert.That(NativeScalarStoreRecovery.MatchesBody(Convert.FromHexString("0004022D021800BDC0035FD6")), Is.False);
    }

    [TestCase("constant", true)]
    [TestCase("void-call", true)]
    [TestCase("double", false)]
    [TestCase("nonzero-integer", false)]
    [TestCase("clobber", false)]
    [TestCase("pointer", false)]
    [TestCase("short-window", false)]
    [TestCase("unaligned", false)]
    [TestCase("abi", false)]
    [TestCase("integer-read", false)]
    [TestCase("wide-read", false)]
    [TestCase("escape", false)]
    [TestCase("receiver-use", false)]
    [TestCase("alias-before", false)]
    [TestCase("zero-init", true)]
    [TestCase("crossing-zero", false)]
    [TestCase("nonzero-init", false)]
    [TestCase("proven-no-input", true)]
    [TestCase("unproven-no-input", false)]
    public void PreserveOnlyProvenNativeScalarEffects(string shape, bool expected)
    {
        Register R(string name) => new(null, name);
        var cfg = new ISILControlFlowGraph([]);
        var block = new Block { ID = 2 }; var next = new Block { ID = 3 };
        cfg.Blocks.AddRange([block, next]);
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, block); Edge(block, next); Edge(next, cfg.ExitBlock);
        if (shape is "zero-init" or "crossing-zero" or "nonzero-init")
            cfg.EntryBlock.Instructions.Add(new Instruction(20, OpCode.Move,
                R(shape == "crossing-zero" ? "stack_-84" : "stack_-80"),
                new Immediate(shape == "nonzero-init" ? 1 : 0)) { NativeWriteSize = 8 });
        var slot = R(shape == "short-window" ? "stack_-8" : shape == "unaligned" ? "stack_-81" : "stack_-80");
        var receiver = new Instruction(0, OpCode.Move, R("X0"),
            shape == "pointer" ? R("X8") : new AddressOf(slot));
        block.Instructions = [receiver,
            new(1, OpCode.Move, R("V0"), new Immediate(0)),
            new(2, OpCode.Move, R("V1"), new FloatLiteral(1)),
            new(3, OpCode.Move, R("V2"), shape == "double" ? new DoubleLiteral(1)
                : shape == "nonzero-integer" ? new Immediate(0x3f800000) : new FloatLiteral(-1))];
        var business = new Instruction(4, OpCode.Move, new MemoryOperand(R("X20"), addend: 0x40), R("V8"));
        block.Instructions.Add(business);
        var args = Enumerable.Range(0, 16).Select(i => (IOperand)R(i < 8 ? "X" + i : "V" + (i - 8))).ToList();
        if (shape == "abi") args[8] = R("X8");
        var call = new Instruction(5, shape == "void-call" ? OpCode.CallVoid : OpCode.Call,
            new Immediate(0x22d2720));
        if (shape != "void-call") call.AddOperands([R("X0")]);
        call.AddOperands(args);
        if (shape == "clobber") block.Instructions.Add(new(6, OpCode.CallVoid, new Immediate(123)));
        if (shape == "alias-before") block.Instructions.Add(new(7, OpCode.Move, R("X9"), R("X0")));
        block.Instructions.Add(call);
        next.Instructions = [new(8, OpCode.Move, R(shape == "integer-read" ? "X10" : "V10"), slot)
            { NativeReadSize = shape == "wide-read" ? 8 : 4 }, new(9, OpCode.Return)];
        if (shape == "escape") next.Instructions.Insert(0, new(10, OpCode.Move, R("X9"), new AddressOf(slot)));
        if (shape == "receiver-use") next.Instructions.Insert(0, new(11, OpCode.Move, R("X9"), R("X0")));
        if (shape is "proven-no-input" or "unproven-no-input")
            next.Instructions.Insert(0, new(21, OpCode.Call, new Immediate(0xaae400), R("X0"), R("X0")));
        foreach (var b in cfg.Blocks) b.CalculateBlockType();
        var serial = 12;
        Assert.That(NativeScalarStoreRecovery.TryRecover(cfg, block, ref serial,
            shape == "proven-no-input" ? i => i.IsCall && i.Operands[0] is Immediate { Value: 0xaae400 } : null), Is.EqualTo(expected));
        Assert.That(block.Instructions.Contains(business), Is.True);
        Assert.That(block.Instructions.Contains(call), Is.EqualTo(!expected));
        if (!expected) { Assert.That(serial, Is.EqualTo(12)); return; }
        Assert.That(block.BlockType, Is.EqualTo(BlockType.Fall));
        Assert.That(block.Instructions.TakeLast(3).Select(i => ((Register)i.Destination!).Name),
            Is.EqualTo(new[] { "stack_-80", "stack_-7C", "stack_-78" }));
        Assert.That(block.Instructions.TakeLast(3).All(i => i.NativeWriteSize == 4 && i.Operands[1] is FloatLiteral), Is.True);
        if (shape == "zero-init")
            Assert.That(cfg.EntryBlock.Instructions.Select(i => ((Register)i.Destination!).Name),
                Is.EqualTo(new[] { "stack_-80", "stack_-7C" }));
    }
}
