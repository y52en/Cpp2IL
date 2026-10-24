using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// ARM logical-register instructions apply ShiftReg BEFORE optional inversion.
// Preserve the exact W/X bit-vector width with explicit scalar conversions.
// LSR is represented by arithmetic shift + a proven mask (no signed-shift
// guess, new opcode, altered executable bytes or managed layout).
public static class Arm64ShiftedLogicalRecovery
{
    public static List<Instruction>? LowerStandalone(Arm64Instruction native,SystemTypesContext types)
    {
        var width=Width(native.Op0Reg);
        if(width==0 || Width(native.Op1Reg)!=width
            || native.Mnemonic is not (Arm64Mnemonic.LSL or Arm64Mnemonic.LSR or Arm64Mnemonic.ASR)
            || native.Op2Kind is not (Arm64OperandKind.Register or Arm64OperandKind.Immediate)
            || native.Op2Kind==Arm64OperandKind.Register && Width(native.Op2Reg)!=width)return null;
        var unsigned=width==4?types.SystemUInt32Type:types.SystemUInt64Type;
        var signed=width==4?types.SystemInt32Type:types.SystemInt64Type;
        var valueType=native.Mnemonic==Arm64Mnemonic.ASR?signed:unsigned;
        var result=new List<Instruction>();
        void Emit(OpCode opcode,params IOperand[] operands)
            =>result.Add(new(result.Count,opcode,operands.ToList()){NativeArithmeticSize=width});
        var input=new Register(null,"SCALAR_SHIFT_INPUT");
        Emit(OpCode.NumericConvert,input,valueType,unsigned,Read(native.Op1Reg));
        IOperand count;
        if(native.Op2Kind==Arm64OperandKind.Register)
        {
            var narrowed=new Register(null,"SCALAR_SHIFT_COUNT");
            // Native and CIL both mask to low5/6 count bits. Reducing a native
            // register count to I4 preserves those bits and makes valid CIL.
            Emit(OpCode.NumericConvert,narrowed,types.SystemInt32Type,unsigned,Read(native.Op2Reg));count=narrowed;
        }
        else
        {
            if(native.Op2Imm<0 || native.Op2Imm>=width*8)return null;
            count=new Immediate(native.Op2Imm);
        }
        var shifted=new Register(null,"SCALAR_SHIFT_RESULT");
        Emit(native.Mnemonic switch{Arm64Mnemonic.LSL=>OpCode.ShiftLeft,
            Arm64Mnemonic.LSR=>OpCode.ShiftRightUnsigned,_=>OpCode.ShiftRight},shifted,input,count);
        var target=Read(native.Op0Reg) is Register register?register:new Register(null,"SCALAR_SHIFT_DISCARDED");
        Emit(OpCode.NumericConvert,target,unsigned,valueType,shifted);
        return result;
    }

    static int Width(Arm64Register register)=>register switch
    {
        >=Arm64Register.W0 and <=Arm64Register.W31=>4,
        >=Arm64Register.X0 and <=Arm64Register.X31=>8,_=>0,
    };
    static IOperand Read(Arm64Register register)
    {
        var number=Width(register)==4?(int)register-(int)Arm64Register.W0:(int)register-(int)Arm64Register.X0;
        return number==31?new Immediate(0):new Register(null,"X"+number);
    }

    public static List<Instruction>? Lower(Arm64Instruction native,SystemTypesContext types)
    {
        var test=native.Mnemonic==Arm64Mnemonic.TST;
        var operation=native.Mnemonic switch
        {
            Arm64Mnemonic.AND or Arm64Mnemonic.ANDS or Arm64Mnemonic.BIC or Arm64Mnemonic.BICS or Arm64Mnemonic.TST=>OpCode.And,
            Arm64Mnemonic.ORR or Arm64Mnemonic.ORN=>OpCode.Or,
            Arm64Mnemonic.EOR or Arm64Mnemonic.EON=>OpCode.Xor,_=>OpCode.Invalid,
        };
        var width=Width(native.Op0Reg);
        var left=test?native.Op0Reg:native.Op1Reg;
        var right=test?native.Op1Reg:native.Op2Reg;
        var shift=test?native.Op2Imm:native.Op3Imm;
        var kind=test?native.Op2Kind:native.Op3Kind;
        // Logical-register decoding stores the modifier on the immediate
        // operand. FinalOpShiftType is NONE even for the real CRC EOR LSR #1.
        var shiftType=test?native.Op2ShiftType:native.Op3ShiftType;
        if(operation==OpCode.Invalid || width==0 || Width(left)!=width || Width(right)!=width
            || kind!=Arm64OperandKind.Immediate || shift<=0 || shift>=width*8
            || shiftType is not (Arm64ShiftType.LSL or Arm64ShiftType.LSR or Arm64ShiftType.ASR or Arm64ShiftType.ROR))return null;
        var unsigned=width==4?types.SystemUInt32Type:types.SystemUInt64Type;
        var signed=width==4?types.SystemInt32Type:types.SystemInt64Type;
        var result=new List<Instruction>();
        Register Temp(string name)=>new(null,"LOGICAL_"+name);
        void Emit(OpCode opcode,params IOperand[] operands)
            =>result.Add(new(result.Count,opcode,operands.ToList()){NativeArithmeticSize=width});
        var a=Temp("LEFT");var b=Temp("RIGHT");
        // W reads consume a 32-bit value. Do not seed a preceding ADD W as
        // UInt64 merely because the lifter normalizes its register name to Xn.
        Emit(OpCode.NumericConvert,a,unsigned,unsigned,Read(left));
        Emit(OpCode.NumericConvert,b,unsigned,unsigned,Read(right));
        IOperand ShiftRightLogical(IOperand value,int amount,string suffix)
        {
            var shifted=Temp("SHR_"+suffix);var masked=Temp("MASK_"+suffix);
            Emit(OpCode.ShiftRight,shifted,value,new Immediate(amount));
            var mask=ulong.MaxValue>>(64-width*8+amount);
            Emit(OpCode.And,masked,shifted,new Immediate(unchecked((long)mask)));
            return masked;
        }
        IOperand shifted;
        if(shiftType==Arm64ShiftType.LSR)shifted=ShiftRightLogical(b,(int)shift,"RIGHT");
        else if(shiftType==Arm64ShiftType.ASR)
        {
            var sign=Temp("SIGNED");var arithmetic=Temp("ASR");
            Emit(OpCode.NumericConvert,sign,signed,unsigned,b);
            Emit(OpCode.ShiftRight,arithmetic,sign,new Immediate(shift));shifted=arithmetic;
        }
        else
        {
            var high=Temp("SHL");Emit(OpCode.ShiftLeft,high,b,new Immediate(shift));
            if(shiftType==Arm64ShiftType.ROR)
            {
                // ROR right n == (x >> n) | (x << (width-n)).
                result.RemoveAt(result.Count-1);
                Emit(OpCode.ShiftLeft,high,b,new Immediate(width*8-shift));
                var low=ShiftRightLogical(b,(int)shift,"ROTATE");
                var rotate=Temp("ROTATE");Emit(OpCode.Or,rotate,low,high);shifted=rotate;
            }
            else shifted=high;
        }
        var normalized=Temp("SHIFTED");Emit(OpCode.NumericConvert,normalized,unsigned,signed,shifted);
        if(native.Mnemonic is Arm64Mnemonic.BIC or Arm64Mnemonic.BICS or Arm64Mnemonic.ORN or Arm64Mnemonic.EON)
        {
            var inverted=Temp("INVERTED");Emit(OpCode.Not,inverted,normalized);normalized=inverted;
        }
        var combined=Temp("RESULT");Emit(operation,combined,a,normalized);
        var destination=test || (int)native.Op0Reg==(int)(width==4?Arm64Register.W31:Arm64Register.X31)
            ? Temp("DISCARDED"):Read(native.Op0Reg);
        Emit(OpCode.NumericConvert,destination,unsigned,signed,combined);
        return result;
    }
}
