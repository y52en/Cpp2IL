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
        Arm64Register Destination, ulong[] Targets, int AddIndex = -1, int GuardIndex = -1);

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
        => RecognizeContiguous(body,start,readOnlyData) ?? RecognizeScheduled(body,start,readOnlyData);

    // Multiple computed jumps are safe only as a CLOSED set: every BR must be
    // a fully range/data/target-proven table, and none may enter another
    // dispatch after its guard. One unresolved indirect entry rejects the set.
    public static IReadOnlyList<Table> RecognizeAll(IReadOnlyList<Arm64Instruction> body,
        Func<ulong,int,byte[]?> readOnlyData)
    {
        var tables=new List<Table>();
        for(var start=0;start<body.Count;start++)
            if((RecognizeContiguous(body,start,readOnlyData,false)
                ?? RecognizeScheduled(body,start,readOnlyData,false)) is { } table)tables.Add(table);
        if(tables.Count==0)return tables;
        var branches=body.Select((i,n)=>(i,n)).Where(p=>p.i.Mnemonic==Arm64Mnemonic.BR).Select(p=>p.n).ToHashSet();
        if(!branches.SetEquals(tables.Select(t=>t.BranchIndex))
            || tables.Select(t=>t.BranchIndex).Distinct().Count()!=tables.Count)return [];
        foreach(var table in tables)
            foreach(var other in tables.Where(t=>!ReferenceEquals(t,table)))
            {
                if(table.GuardIndex<=other.BranchIndex && other.GuardIndex<=table.BranchIndex)return [];
                var from=body[other.GuardIndex].Address;var through=body[other.BranchIndex].Address;
                if(table.Targets.Any(target=>target>=from && target<=through))return [];
            }
        return tables;
    }

    private static Table? RecognizeContiguous(IReadOnlyList<Arm64Instruction> body, int start,
        Func<ulong, int, byte[]?> readOnlyData, bool rejectOtherComputedJumps=true)
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
            if (rejectOtherComputedJumps && instruction.Mnemonic == Arm64Mnemonic.BR && i != start + 6) return null;
            ulong? target = instruction.Mnemonic switch
            {
                Arm64Mnemonic.B or Arm64Mnemonic.BL => instruction.BranchTarget,
                Arm64Mnemonic.BC => instruction.Op0PcRelImm,
                Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ => unchecked((ulong)((long)instruction.Address + instruction.Op1Imm)),
                Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ => unchecked((ulong)((long)instruction.Address + instruction.Op2Imm)),
                _ => null,
            };
            if (target >= cmp.Address && target <= branch.Address) return null;
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
        return new(start + 4, start + 6, load.MemAddendReg, load.Op0Reg, targets,GuardIndex:start);
    }

    // Original ApplyCurve uses CMP W1 followed by an explicit MOV W8,W1,
    // and schedules an FMOV between the immutable table read and target ADD.
    // Keep those independent instructions; never infer the high Xn bits from
    // CMP Wn alone or silently skip calls/loads/stores while matching a table.
    private static Table? RecognizeScheduled(IReadOnlyList<Arm64Instruction> body,int start,
        Func<ulong,int,byte[]?> readOnlyData,bool rejectOtherComputedJumps=true)
    {
        if(start<0 || start+7>=body.Count)return null;
        var cmp=body[start];var guard=body[start+1];
        if(cmp.Mnemonic!=Arm64Mnemonic.CMP || cmp.Op0Reg is < Arm64Register.W0 or > Arm64Register.W30
            || cmp.Op1Kind!=Arm64OperandKind.Immediate || cmp.Op1Imm is <1 or >4095
            || guard.Address!=cmp.Address+4
            || guard.Mnemonic!=Arm64Mnemonic.B || guard.MnemonicConditionCode!=Arm64ConditionCode.HI)return null;
        Arm64Instruction? page=null,address=null;var copied=Arm64Register.INVALID;var loadIndex=-1;
        var at=start+2;
        for(;at<body.Count && at<=start+8;at++)
        {
            var i=body[at];
            if(i.Address!=cmp.Address+(ulong)(4*(at-start)))return null;
            if(i.Mnemonic==Arm64Mnemonic.LDRSW){loadIndex=at;break;}
            if(IndependentConstant(i))continue;
            if(page==null && i.Mnemonic==Arm64Mnemonic.ADRP
                && i.Op0Reg is >= Arm64Register.X0 and <= Arm64Register.X30){page=i;continue;}
            if(address==null && page!=null && i.Mnemonic==Arm64Mnemonic.ADD
                && i.Op0Reg==page.Value.Op0Reg && i.Op1Reg==page.Value.Op0Reg
                && i.Op2Kind==Arm64OperandKind.Immediate && i.Op2Imm is >=0 and <=4095
                && !(i.Op3Kind==Arm64OperandKind.Immediate && i.Op3Imm!=0)){address=i;continue;}
            if(copied==Arm64Register.INVALID && i.Mnemonic==Arm64Mnemonic.MOV
                && i.Op0Reg is >= Arm64Register.W0 and <= Arm64Register.W30
                && i.Op1Kind==Arm64OperandKind.Register && i.Op1Reg==cmp.Op0Reg)
            {copied=Arm64Register.X0+(i.Op0Reg-Arm64Register.W0);continue;}
            return null;
        }
        if(loadIndex<0 || page==null || address==null || copied==Arm64Register.INVALID)return null;
        var load=body[loadIndex];
        if(load.MemBase!=page.Value.Op0Reg || load.MemIndexMode!=Arm64MemoryIndexMode.Offset
            || load.MemOffset!=0 || load.MemExtendOrShiftAmount!=2
            || load.MemAddendReg!=copied || load.Op0Reg is < Arm64Register.X0 or > Arm64Register.X30
            || page.Value.Op0Reg==copied || page.Value.Op0Reg==load.Op0Reg
            || page.Value.Op0Reg==Arm64Register.X0+(cmp.Op0Reg-Arm64Register.W0))return null;
        var addIndex=-1;var branchIndex=-1;
        for(at=loadIndex+1;at<body.Count && at<=loadIndex+5;at++)
        {
            var i=body[at];
            if(i.Address!=cmp.Address+(ulong)(4*(at-start)))return null;
            if(IndependentConstant(i))continue;
            if(addIndex<0 && i.Mnemonic==Arm64Mnemonic.ADD && i.Op0Reg==load.Op0Reg && i.Op1Reg==load.Op0Reg
                && i.Op2Kind==Arm64OperandKind.Register && i.Op2Reg==page.Value.Op0Reg
                && !(i.Op3Kind==Arm64OperandKind.Immediate && i.Op3Imm!=0)
                && i.FinalOpExtendType==Arm64ExtendType.NONE){addIndex=at;continue;}
            if(addIndex>=0 && i.Mnemonic==Arm64Mnemonic.BR && i.Op0Reg==load.Op0Reg){branchIndex=at;break;}
            return null;
        }
        if(branchIndex<0)return null;
        var branch=body[branchIndex];var nativeAddresses=body.Select(i=>i.Address).ToHashSet();
        if(!nativeAddresses.Contains(guard.BranchTarget) || guard.BranchTarget<=branch.Address)return null;
        foreach(var i in body)
        {
            if(rejectOtherComputedJumps && i.Mnemonic==Arm64Mnemonic.BR && i.Address!=branch.Address)return null;
            ulong? target=i.Mnemonic switch
            {
                Arm64Mnemonic.B or Arm64Mnemonic.BL=>i.BranchTarget,
                Arm64Mnemonic.BC=>i.Op0PcRelImm,
                Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ=>unchecked((ulong)((long)i.Address+i.Op1Imm)),
                Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ=>unchecked((ulong)((long)i.Address+i.Op2Imm)),
                _=>null
            };
            if(target>=cmp.Address && target<=branch.Address)return null;
        }
        var tableAddress=unchecked((ulong)((long)(page.Value.Address&~0xfffUL)+page.Value.Op1Imm+address.Value.Op2Imm));
        var count=checked((int)cmp.Op1Imm+1);var bytes=readOnlyData(tableAddress,count*4);
        if(bytes==null || bytes.Length!=count*4)return null;
        var targets=new ulong[count];
        for(var n=0;n<count;n++)
        {
            var target=unchecked((ulong)((long)tableAddress+BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(n*4,4))));
            if((target&3)!=0 || !nativeAddresses.Contains(target) || target>=cmp.Address && target<=branch.Address)return null;
            targets[n]=target;
        }
        return new(loadIndex,branchIndex,copied,load.Op0Reg,targets,addIndex,start);
    }

    private static bool IndependentConstant(Arm64Instruction i)
        => i.Mnemonic==Arm64Mnemonic.NOP || i.Mnemonic==Arm64Mnemonic.FMOV
            && i.Op1Kind==Arm64OperandKind.FloatingPointImmediate
            && (i.Op0Reg is >=Arm64Register.S0 and <=Arm64Register.S31
                || i.Op0Reg is >=Arm64Register.D0 and <=Arm64Register.D31);
}
