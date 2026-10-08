using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Disarm;
using Disarm.InternalDisassembly;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.InstructionSets;

public static class Arm64JumpTableRecovery
{
    public sealed record Table(int LoadIndex, int BranchIndex, Arm64Register Selector,
        Arm64Register Destination, ulong[] Targets);

    public static void Emit(Table table, ulong nativeAddress, List<Instruction> instructions, List<ulong> addresses)
    {
        Register Reg(Arm64Register register) => new(null, "X" + (register - Arm64Register.X0));
        var selector = new Register(null, "jump_table_selector_" + nativeAddress);
        void Add(OpCode op, params List<IOperand> operands)
        {
            addresses.Add(nativeAddress);
            instructions.Add(new(instructions.Count, op, operands));
        }
        Add(OpCode.Move, selector, Reg(table.Selector));
        for (var entry = 0; entry < table.Targets.Length; entry++)
        {
            Add(OpCode.Move, Reg(table.Destination), new Immediate(unchecked((long)table.Targets[entry])));
            if (entry == table.Targets.Length - 1)
                Add(OpCode.Jump, new Immediate(unchecked((long)table.Targets[entry])));
            else
            {
                var condition = new Register(null, "jump_table_case_" + nativeAddress + "_" + entry);
                Add(OpCode.CheckEqual, condition, selector, new Immediate(entry));
                Add(OpCode.ConditionalJump, new Immediate(unchecked((long)table.Targets[entry])), condition);
            }
        }
    }

    // Recognize actual machine instructions before CFG removes switch arms.
    // The callback must read only immutable, file-backed native image bytes.
    public static Table? Recognize(IReadOnlyList<Arm64Instruction> body, int start,
        Func<ulong, int, byte[]?> readOnlyData)
    {
        if (start < 1 || start + 6 >= body.Count) return null;
        var cmp = body[start]; var guard = body[start + 1];
        var page = body[start + 2]; var address = body[start + 3];
        var load = body[start + 4]; var add = body[start + 5]; var branch = body[start + 6];
        if (Enumerable.Range(1, 6).Any(i => body[start + i].Address != cmp.Address + (ulong)(4 * i))) return null;
        if (cmp.Mnemonic != Arm64Mnemonic.CMP || cmp.Op0Reg is < Arm64Register.W0 or > Arm64Register.W30
            || cmp.Op1Kind != Arm64OperandKind.Immediate || cmp.Op1Imm is < 1 or > 4095
            || guard.Mnemonic != Arm64Mnemonic.B || guard.MnemonicConditionCode != Arm64ConditionCode.HI
            || page.Mnemonic != Arm64Mnemonic.ADRP || page.Op0Reg is < Arm64Register.X0 or > Arm64Register.X30
            || address.Mnemonic != Arm64Mnemonic.ADD || address.Op0Reg != page.Op0Reg || address.Op1Reg != page.Op0Reg
            || address.Op2Kind != Arm64OperandKind.Immediate || address.Op2Imm is < 0 or > 4095
            || address.Op3Kind == Arm64OperandKind.Immediate && address.Op3Imm != 0
            || load.Mnemonic != Arm64Mnemonic.LDRSW || load.MemBase != page.Op0Reg
            || load.MemIndexMode != Arm64MemoryIndexMode.Offset || load.MemOffset != 0
            || load.MemExtendOrShiftAmount != 2 || load.Op0Reg is < Arm64Register.X0 or > Arm64Register.X30
            || load.MemAddendReg != Arm64Register.X0 + (cmp.Op0Reg - Arm64Register.W0)
            || page.Op0Reg == load.MemAddendReg || page.Op0Reg == load.Op0Reg
            || add.Mnemonic != Arm64Mnemonic.ADD || add.Op0Reg != load.Op0Reg || add.Op1Reg != load.Op0Reg
            || add.Op2Kind != Arm64OperandKind.Register || add.Op2Reg != page.Op0Reg
            || add.Op3Kind == Arm64OperandKind.Immediate && add.Op3Imm != 0
            || add.FinalOpExtendType != Arm64ExtendType.NONE
            || branch.Mnemonic != Arm64Mnemonic.BR || branch.Op0Reg != load.Op0Reg) return null;
        // CMP Wn alone does not prove the Xn index's high bits are zero.
        var seed = body[start - 1];
        if (seed.Address + 4 != cmp.Address || seed.Op0Reg != cmp.Op0Reg
            || seed.Mnemonic is not (Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.MOV
                or Arm64Mnemonic.MOVZ or Arm64Mnemonic.ADD or Arm64Mnemonic.SUB
                or Arm64Mnemonic.AND or Arm64Mnemonic.ORR or Arm64Mnemonic.EOR)) return null;
        var nativeAddresses = body.Select(i => i.Address).ToHashSet();
        if (!nativeAddresses.Contains(guard.BranchTarget) || guard.BranchTarget <= branch.Address) return null;
        // A second computed jump or any entry into the middle defeats this
        // local range-check proof. Reject instead of silently losing an edge.
        for (var i = 0; i < body.Count; i++)
        {
            var instruction = body[i];
            if (instruction.Mnemonic == Arm64Mnemonic.BR && i != start + 6) return null;
            if (instruction.Mnemonic is Arm64Mnemonic.B or Arm64Mnemonic.BC or Arm64Mnemonic.BL
                or Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ)
                if (instruction.BranchTarget >= cmp.Address && instruction.BranchTarget <= branch.Address) return null;
        }
        var tableAddress = unchecked((ulong)((long)(page.Address & ~0xfffUL) + page.Op1Imm + address.Op2Imm));
        var count = checked((int)cmp.Op1Imm + 1);
        var bytes = readOnlyData(tableAddress, count * 4);
        if (bytes == null || bytes.Length != count * 4) return null;
        var targets = new ulong[count];
        for (var i = 0; i < count; i++)
        {
            var offset = BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(i * 4, 4));
            var target = unchecked((ulong)((long)tableAddress + offset));
            if ((target & 3) != 0 || !nativeAddresses.Contains(target)
                || target >= cmp.Address && target <= branch.Address) return null;
            targets[i] = target;
        }
        return new(start + 4, start + 6, load.MemAddendReg, load.Op0Reg, targets);
    }
}
