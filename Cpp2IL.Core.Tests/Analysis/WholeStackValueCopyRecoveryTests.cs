using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class WholeStackValueCopyRecoveryTests
{
    private static Register R(string name) => new(null, name);
    private static List<Instruction> Copy(string variant = "complete")
    {
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, R("X8"), R("stack_-A8")) { NativeReadSize = 8 },
            new(1, OpCode.Move, R("V0"), R("stack_-B8")) { NativeReadSize = 16 },
            new(2, OpCode.Move, R("V1"), R("stack_-C8")) { NativeReadSize = 16 },
            new(3, OpCode.Move, R("X25"), new MemoryOperand(addend:0x1234)),
            new(4, OpCode.Move, R("stack_-70"), R("X8")) { NativeWriteSize = 8 },
            new(5, OpCode.Move, R("stack_-90"), R("V1")) { NativeWriteSize = 16 },
            new(6, OpCode.Move, R("stack_-80"), R("V0")) { NativeWriteSize = 16 },
            variant == "live" ? new(7, OpCode.Return, R("V1")) : new(7, OpCode.Return)
        };
        if (variant == "missing") instructions.RemoveAt(4);
        if (variant == "width") instructions[6].NativeWriteSize = 8;
        if (variant == "overlap") instructions[4].SetOperand(0, R("stack_-A8"));
        if (variant == "unknown") instructions[3] = new(3, OpCode.Move, new MemoryOperand(R("X2")), R("X3"));
        return instructions;
    }

    [Test]
    public void AllFortyNativeBytesBecomeOneLogicalCopyWithoutInventingWidth()
    {
        var instructions = Copy(); var graph = new ISILControlFlowGraph(instructions);
        var block = graph.Blocks.Single(b => b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph, block, 0, R("stack_-C8"), 40), Is.True);
        Assert.That(instructions[4].Operands[0], Is.EqualTo(R("stack_-90")));
        Assert.That(instructions[4].Operands[1], Is.EqualTo(R("stack_-C8")));
        Assert.That(instructions[4].NativeWriteSize, Is.Zero);
        Assert.That(instructions.Take(3).All(i => i.OpCode == OpCode.Move), Is.True);
        Assert.That(instructions.Skip(5).Take(2).All(i => i.OpCode == OpCode.Nop), Is.True);
        Assert.That(instructions[3].OpCode, Is.EqualTo(OpCode.Move));
    }

    [TestCase("missing")]
    [TestCase("width")]
    [TestCase("overlap")]
    [TestCase("unknown")]
    public void IncompleteAliasedOrStillLiveChunksRemainUnmodified(string variant)
    {
        var instructions = Copy(variant); var before = instructions.Select(i => i.ToString()).ToArray();
        var graph = new ISILControlFlowGraph(instructions);
        var block = graph.Blocks.Single(b => b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph, block, 0, R("stack_-C8"), 40), Is.False);
        Assert.That(instructions.Select(i => i.ToString()), Is.EqualTo(before));
    }

    [Test]
    public void AdditionalRegisterConsumerKeepsItsOriginalNativeLoadValue()
    {
        var instructions = Copy("live"); var graph = new ISILControlFlowGraph(instructions);
        var block = graph.Blocks.Single(b => b.Instructions.Contains(instructions[0]));
        Assert.That(WholeStackValueCopyRecovery.Recover(graph, block, 0, R("stack_-C8"), 40), Is.True);
        Assert.That(instructions[2].OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(instructions[2].NativeReadSize, Is.EqualTo(16));
        Assert.That(instructions[7].Operands[0], Is.EqualTo(R("V1")));
    }
}
