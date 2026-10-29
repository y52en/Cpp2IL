using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// CMN is ADDS to ZR, not subtraction of a negated operand: that substitution
// has different V/C flags at signed minimum. All intermediate words are typed,
// wrapped and explicitly converted; input W views never retag whole producers.
public static class Arm64ScalarTestFlags
{
    private static int Width(Arm64Register register)=>register switch
    {
        >=Arm64Register.W0 and <=Arm64Register.W31=>4,
        >=Arm64Register.X0 and <=Arm64Register.X31=>8,_=>0,
    };
    private static IOperand Read(Arm64Register register)
    {
        var number=(int)register-(int)(Width(register)==4?Arm64Register.W0:Arm64Register.X0);
        return number==31?new Immediate(0):new Register(null,"X"+number);
    }

    public static List<Instruction>? Lower(Arm64Instruction native,SystemTypesContext types)
    {
        var addition=native.Mnemonic is Arm64Mnemonic.CMN or Arm64Mnemonic.ADDS;
        if(!addition && native.Mnemonic is not (Arm64Mnemonic.TST or Arm64Mnemonic.ANDS))return null;
        var alias=native.Mnemonic is Arm64Mnemonic.CMN or Arm64Mnemonic.TST;
        var left=alias?native.Op0Reg:native.Op1Reg;
        var rightKind=alias?native.Op1Kind:native.Op2Kind;
        var rightReg=alias?native.Op1Reg:native.Op2Reg;
        var rightImmediate=alias?native.Op1Imm:native.Op2Imm;
        var modifierKind=alias?native.Op2Kind:native.Op3Kind;
        var width=Width(left);
        if(width==0 || native.Op0Kind!=Arm64OperandKind.Register || !alias && Width(native.Op0Reg)!=width)return null;
        var extended=native.FinalOpExtendType!=Arm64ExtendType.NONE;
        if(extended && (!addition || width!=8 || native.FinalOpExtendType is not (Arm64ExtendType.UXTW or Arm64ExtendType.SXTW)))return null;
        var immediate=rightKind==Arm64OperandKind.Immediate;
        if(extended && (immediate || left is Arm64Register.W31 or Arm64Register.X31))return null;
        if(!immediate && (rightKind!=Arm64OperandKind.Register || Width(rightReg)!=(extended?4:width)))return null;
        // ADDS immediate Rn31 denotes SP; do not substitute ZR for its address.
        if(addition && immediate && left is Arm64Register.W31 or Arm64Register.X31)return null;
        var shift=modifierKind==Arm64OperandKind.Immediate?(alias?native.Op2Imm:native.Op3Imm):0;
        var operandShift=alias?native.Op2ShiftType:native.Op3ShiftType;
        // Disarm arithmetic modifiers use FinalOpShiftType; logical-register
        // modifiers can instead live on the immediate operand itself.
        if(operandShift!=Arm64ShiftType.NONE && native.FinalOpShiftType!=Arm64ShiftType.NONE
            && operandShift!=native.FinalOpShiftType)return null;
        var shiftType=operandShift!=Arm64ShiftType.NONE?operandShift:native.FinalOpShiftType;
        if(extended)
        {
            // ExtendReg applies its optional LSL AFTER the W truncation and
            // signed/unsigned extension. Rn31 means SP, rejected above.
            if(shift is <0 or >4 || shiftType is not (Arm64ShiftType.NONE or Arm64ShiftType.LSL))return null;
            shiftType=Arm64ShiftType.LSL;
        }
        if(modifierKind!=default && modifierKind!=Arm64OperandKind.Immediate)return null;
        if(shift<0 || shift>=width*8 || shift!=0 && shiftType is not (Arm64ShiftType.LSL or Arm64ShiftType.LSR or Arm64ShiftType.ASR or Arm64ShiftType.ROR))return null;
        if(addition && shiftType==Arm64ShiftType.ROR)return null;
        if(immediate && shift!=0 && (!addition || shiftType!=Arm64ShiftType.LSL || shift!=12))return null;
        var word=width==4?types.SystemUInt32Type:types.SystemUInt64Type;
        var signed=width==4?types.SystemInt32Type:types.SystemInt64Type;
        var result=new List<Instruction>();var sequence=0;
        Register Temp(string role)=>new(null,"TEST_FLAGS_"+role+"_"+sequence++);
        Instruction Emit(OpCode opcode,params IOperand[] operands)
        {
            var instruction=new Instruction(result.Count,opcode,operands.ToList());result.Add(instruction);return instruction;
        }
        Register View(IOperand source,string role)
        {
            var value=Temp(role);
            Emit(OpCode.NumericConvert,value,word,types.SystemUInt64Type,source).NativeIntegerSourceView=width==4;
            return value;
        }
        Register Binary(OpCode opcode,IOperand left,IOperand right,string role,TypeAnalysisContext? rawType=null)
        {
            var raw=Temp(role+"_RAW");var value=Temp(role);
            Emit(opcode,raw,left,right).NativeArithmeticSize=width;
            Emit(OpCode.NumericConvert,value,word,rawType??word,raw);
            return value;
        }
        var a=View(Read(left),"LEFT");
        IOperand right=immediate?new Immediate(rightImmediate):Read(rightReg);
        if(extended)
        {
            var signExtend=native.FinalOpExtendType==Arm64ExtendType.SXTW;
            var narrowType=signExtend?types.SystemInt32Type:types.SystemUInt32Type;
            var wideType=signExtend?types.SystemInt64Type:types.SystemUInt64Type;
            var narrow=Temp("EXTEND_NARROW");var expanded=Temp("EXTENDED");
            Emit(OpCode.NumericConvert,narrow,narrowType,types.SystemUInt64Type,right).NativeIntegerSourceView=true;
            Emit(OpCode.NumericConvert,expanded,wideType,narrowType,narrow);
            right=expanded;
        }
        var b=View(right,"RIGHT");
        if(shift!=0)
        {
            if(shiftType==Arm64ShiftType.ASR)
            {
                var interpreted=Temp("SIGNED_RIGHT");Emit(OpCode.NumericConvert,interpreted,signed,word,b);
                b=Binary(OpCode.ShiftRight,interpreted,new Immediate(shift),"SHIFTED",signed);
            }
            else if(shiftType==Arm64ShiftType.ROR)
            {
                var low=Binary(OpCode.ShiftRightUnsigned,b,new Immediate(shift),"ROTATE_LOW");
                var high=Binary(OpCode.ShiftLeft,b,new Immediate(width*8-shift),"ROTATE_HIGH");
                b=Binary(OpCode.Or,low,high,"ROTATED");
            }
            else b=Binary(shiftType==Arm64ShiftType.LSR?OpCode.ShiftRightUnsigned:OpCode.ShiftLeft,b,new Immediate(shift),"SHIFTED");
        }
        var tested=Binary(addition?OpCode.Add:OpCode.And,a,b,"RESULT");
        if(!alias && Read(native.Op0Reg) is Register architecturalDestination)
            Emit(OpCode.NumericConvert,architecturalDestination,word,word,tested);
        void Flag(string name,OpCode opcode,IOperand left,IOperand right,bool unsigned=false)
        {
            var instruction=Emit(opcode,new Register(null,name),left,right);
            instruction.NativeComparisonSize=width;instruction.UnsignedComparison=unsigned;
        }
        Flag("N",OpCode.CheckLess,tested,new Immediate(0));
        Flag("Z",OpCode.CheckEqual,tested,new Immediate(0));
        if(!addition)
        {
            Emit(OpCode.Move,new Register(null,"C"),new Immediate(0));
            Emit(OpCode.Move,new Register(null,"V"),new Immediate(0));
        }
        else
        {
            Flag("C",OpCode.CheckLess,tested,a,true);
            var leftSign=Binary(OpCode.Xor,a,tested,"LEFT_CHANGED_SIGN");
            var rightSign=Binary(OpCode.Xor,b,tested,"RIGHT_CHANGED_SIGN");
            var overflow=Binary(OpCode.And,leftSign,rightSign,"OVERFLOW");
            Flag("V",OpCode.CheckLess,overflow,new Immediate(0));
        }
        return result;
    }
}
