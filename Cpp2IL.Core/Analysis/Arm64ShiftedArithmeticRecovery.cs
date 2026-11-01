using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// ShiftReg is part of an arithmetic register operand, not a decoration.
// Keep the native W/X bit vector and signed ASR view explicit. Leave existing
// unshifted, LSL, extended-register and separately proved ADDS paths unchanged.
public static class Arm64ShiftedArithmeticRecovery
{
    public static (List<Instruction> Operations, Register Operand)? LowerRight(
        Arm64Instruction native, SystemTypesContext types)
    {
        var compare = native.Mnemonic == Arm64Mnemonic.CMP;
        if (!compare && native.Mnemonic is not (Arm64Mnemonic.ADD or Arm64Mnemonic.SUB or Arm64Mnemonic.SUBS))
            return null;
        var width = Width(native.Op0Reg);
        var left = compare ? native.Op0Reg : native.Op1Reg;
        var right = compare ? native.Op1Reg : native.Op2Reg;
        var rightKind = compare ? native.Op1Kind : native.Op2Kind;
        // Disarm's CMP alias moves Rn/Rm but retains the original Op3
        // modifier when Op2 becomes None. Do not silently turn it into #0.
        var retainedModifier = compare && native.Op2Kind == default && native.Op3Kind == Arm64OperandKind.Immediate;
        var compactCompare = compare && !retainedModifier;
        var amount = compactCompare ? native.Op2Imm : native.Op3Imm;
        var amountKind = compactCompare ? native.Op2Kind : native.Op3Kind;
        var shift = compactCompare ? native.Op2ShiftType : native.Op3ShiftType;
        if (shift == Arm64ShiftType.NONE) shift = native.FinalOpShiftType;
        if (width == 0 || Width(left) != width || Width(right) != width
            || rightKind != Arm64OperandKind.Register || amountKind != Arm64OperandKind.Immediate
            || native.FinalOpExtendType != Arm64ExtendType.NONE
            || shift is not (Arm64ShiftType.LSR or Arm64ShiftType.ASR)
            || amount <= 0 || amount >= width * 8)
            return null;
        var unsigned = width == 4 ? types.SystemUInt32Type : types.SystemUInt64Type;
        var signed = width == 4 ? types.SystemInt32Type : types.SystemInt64Type;
        var view = shift == Arm64ShiftType.ASR ? signed : unsigned;
        var number = (int)right - (int)(width == 4 ? Arm64Register.W0 : Arm64Register.X0);
        IOperand input = number == 31 ? new Immediate(0) : new Register(null, "X" + number);
        var read = new Register(null, "ARITH_RIGHT_VIEW");
        var shifted = new Register(null, "ARITH_RIGHT_SHIFTED");
        var result = new Register(null, "ARITH_RIGHT_BITS");
        var operations = new List<Instruction>
        {
            new(0, OpCode.NumericConvert, read, view, unsigned, input)
                {NativeArithmeticSize = width, NativeIntegerSourceView = true},
            new(1, shift == Arm64ShiftType.LSR ? OpCode.ShiftRightUnsigned : OpCode.ShiftRight,
                shifted, read, new Immediate(amount)) {NativeArithmeticSize = width},
            new(2, OpCode.NumericConvert, result, unsigned, view, shifted) {NativeArithmeticSize = width},
        };
        return (operations, result);
    }

    static int Width(Arm64Register register) => register switch
    {
        >= Arm64Register.W0 and <= Arm64Register.W31 => 4,
        >= Arm64Register.X0 and <= Arm64Register.X31 => 8,
        _ => 0,
    };
}
