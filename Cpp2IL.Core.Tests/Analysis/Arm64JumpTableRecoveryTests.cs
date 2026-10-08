using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Disarm;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64JumpTableRecoveryTests
{
    // Actual Android bytes at RVA182FB5C. Addresses are RVAs, not Ghidra's +1MB overlay.
    private static readonly byte[] Native = Convert.FromHexString("681a40b91f250071c82a0054696a00f029f10c912879a8b80801098b00011fd6");
    private const ulong Base = 0x257e33c;
    private static readonly int[] Offsets = [-13952960, -13952516, -13952380, -13951616, -13952252,
        -13951616, -13952116, -13952040, -13951960, -13951876];

    private static List<Arm64Instruction> Body(byte[]? bytes = null)
    {
        var body = Disassembler.Disassemble(bytes ?? Native, 0x182fb5c, new(true, true, false)).ToList();
        foreach (var target in Offsets.Select(o => unchecked((ulong)((long)Base + o))).Distinct())
            body.AddRange(Disassembler.Disassemble(Convert.FromHexString("1f2003d5"), target, new(true, true, false)));
        return body;
    }

    private static byte[] Data(int[]? offsets = null)
    {
        var values = offsets ?? Offsets;
        var data = new byte[values.Length * 4];
        for (var i = 0; i < values.Length; i++) BinaryPrimitives.WriteInt32LittleEndian(data.AsSpan(i * 4, 4), values[i]);
        return data;
    }

    [Test]
    public void RealRelativeTablePreservesNegativeOffsetsAndRepeatedDefault()
    {
        var table = Arm64JumpTableRecovery.Recognize(Body(), 1, (address, count) =>
        {
            Assert.That(address, Is.EqualTo(Base)); Assert.That(count, Is.EqualTo(40)); return Data();
        });
        Assert.That(table, Is.Not.Null);
        Assert.That(table!.LoadIndex, Is.EqualTo(5)); Assert.That(table.BranchIndex, Is.EqualTo(7));
        Assert.That(table.Targets, Is.EqualTo(new ulong[]{0x182fb7c,0x182fd38,0x182fdc0,0x18300bc,
            0x182fe40,0x18300bc,0x182fec8,0x182ff14,0x182ff64,0x182ffb8}));
    }

    [Test]
    public void EmittedDispatchSelectsEveryEdgeAndPreservesAliasedNativeTargetRegister()
    {
        var table = Arm64JumpTableRecovery.Recognize(Body(), 1, (_, _) => Data())!;
        var instructions = new List<Instruction>(); var addresses = new List<ulong>();
        Arm64JumpTableRecovery.Emit(table, 0x182fb70, instructions, addresses);
        Assert.That(addresses.Count, Is.EqualTo(instructions.Count));
        Assert.That(addresses.All(a => a == 0x182fb70), Is.True);
        for (var entry = 0; entry < 10; entry++)
        {
            var registers = new Dictionary<string, long> { ["X8"] = entry };
            long Read(IOperand operand) => operand is Immediate immediate ? immediate.Value : registers[((Register)operand).Name];
            ulong? selected = null;
            foreach (var instruction in instructions)
            {
                var operands = instruction.Operands;
                if (instruction.OpCode == OpCode.Move) registers[((Register)operands[0]).Name] = Read(operands[1]);
                else if (instruction.OpCode == OpCode.CheckEqual) registers[((Register)operands[0]).Name] = Read(operands[1]) == Read(operands[2]) ? 1 : 0;
                else if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump && Read(operands[1]) != 0)
                { selected = ((Immediate)operands[0]).UnsignedValue; break; }
            }
            Assert.That(selected, Is.EqualTo(table.Targets[entry]));
            Assert.That(unchecked((ulong)registers["X8"]), Is.EqualTo(table.Targets[entry]));
        }
    }

    [Test]
    public void ActualCfgRetainsAllTableArmsIncludingRepeatedDestinations()
    {
        var table = Arm64JumpTableRecovery.Recognize(Body(), 1, (_, _) => Data())!;
        var instructions = new List<Instruction>(); var addresses = new List<ulong>();
        Arm64JumpTableRecovery.Emit(table, 0x182fb70, instructions, addresses);
        var targets = new Dictionary<ulong, Instruction>();
        foreach (var target in table.Targets.Distinct())
        {
            var instruction = new Instruction(instructions.Count, OpCode.Return, new Immediate(unchecked((long)target)));
            instructions.Add(instruction); targets[target] = instruction;
        }
        foreach (var instruction in instructions.Where(i => i.OpCode is OpCode.Jump or OpCode.ConditionalJump))
            instruction.SetOperand(0, targets[((Immediate)instruction.Operands[0]).UnsignedValue]);
        var graph = new ISILControlFlowGraph(instructions);
        graph.RemoveUnreachableBlocks();
        Assert.That(graph.Instructions.Count(i => i.OpCode == OpCode.Return), Is.EqualTo(targets.Count));
        Assert.That(targets.Values.All(t => graph.Instructions.Contains(t)), Is.True);
    }

    [TestCase("missing")]
    [TestCase("truncated")]
    [TestCase("unaligned")]
    [TestCase("external")]
    [TestCase("middle")]
    public void UnprovenDataAndTargetsAreNotRecovered(string shape)
    {
        var offsets = (int[])Offsets.Clone();
        if (shape == "unaligned") offsets[0]++;
        if (shape == "external") offsets[0] = 0;
        if (shape == "middle") offsets[0] = unchecked((int)(0x182fb70L - (long)Base));
        var data = shape == "missing" ? null : shape == "truncated" ? new byte[39] : Data(offsets);
        Assert.That(Arm64JumpTableRecovery.Recognize(Body(), 1, (_, _) => data), Is.Null);
    }

    [TestCase("signed-guard")]
    [TestCase("wide-index")]
    [TestCase("wrong-scale")]
    [TestCase("changed-add")]
    public void ModifiedMachineShapesAreNotGuessed(string shape)
    {
        var bytes = (byte[])Native.Clone();
        if (shape == "signed-guard") bytes[8] = 0xcc; // b.gt, not unsigned b.hi
        if (shape == "wide-index") bytes[3] = 0xf9; // ldr x8, not zero-extending ldr w8
        if (shape == "wrong-scale") bytes[21] = 0x69; // remove register-index scale bit
        if (shape == "changed-add") bytes[24] = 0x01; // writes x1 instead of x8
        Assert.That(Arm64JumpTableRecovery.Recognize(Body(bytes), 1, (_, _) => Data()), Is.Null);
    }

    [TestCase("fcffff17")]
    [TestCase("f8ffff17")]
    public void ForeignEntryIntoRangeCheckedRegionIsRejected(string branchBytes)
    {
        var body = Body();
        // b to 182FB70, entering at the table load after the range check.
        body.AddRange(Disassembler.Disassemble(Convert.FromHexString(branchBytes), 0x182fb80, new(true,true,false)));
        Assert.That(Arm64JumpTableRecovery.Recognize(body, 1, (_, _) => Data()), Is.Null);
    }

    [TestCase(0x34000000u, false)]
    [TestCase(0x35000000u, false)]
    [TestCase(0x36000000u, false)]
    [TestCase(0x37000000u, false)]
    [TestCase(0x34000000u, true)]
    [TestCase(0x35000000u, true)]
    [TestCase(0x36000000u, true)]
    [TestCase(0x37000000u, true)]
    public void CompareAndTestBranchesUseTheirActualRelativeOperand(uint opcode, bool entersRegion)
    {
        var body = Body();
        const ulong from = 0x1830100;
        var target = entersRegion ? 0x182fb60UL : 0x18300bcUL;
        var immediate = unchecked((uint)(((long)target - (long)from) / 4));
        var mask = opcode is 0x36000000u or 0x37000000u ? 0x3fffu : 0x7ffffu;
        var bytes = new byte[4]; BinaryPrimitives.WriteUInt32LittleEndian(bytes, opcode | ((immediate & mask) << 5));
        body.AddRange(Disassembler.Disassemble(bytes, from, new(true,true,false)));
        var table = Arm64JumpTableRecovery.Recognize(body, 1, (_, _) => Data());
        Assert.That(table != null, Is.EqualTo(!entersRegion));
    }
}
