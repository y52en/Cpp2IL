using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// SBF(M) aliases sign-extend the extracted field, not the source register.
// Explicit conversions preserve W overflow before the arithmetic shift and
// zero-extension on a W destination. Never shift by 32/64 (CIL masks counts).
public static class Arm64BitfieldExtractRecovery
{
    private static int Width(Arm64Register r)=>r switch {
        >=Arm64Register.W0 and <=Arm64Register.W31=>4,
        >=Arm64Register.X0 and <=Arm64Register.X31=>8,_=>0};
    private static IOperand Read(Arm64Register r,int width)
    {
        var index=(int)r-(int)(width==4?Arm64Register.W0:Arm64Register.X0);
        return index==31?new Immediate(0):new Register(null,"X"+index);
    }

    public static List<Instruction>? Lower(Arm64Instruction native,SystemTypesContext types)
    {
        var width=Width(native.Op0Reg);var bits=width*8;
        if(native.Mnemonic is not (Arm64Mnemonic.UBFX or Arm64Mnemonic.SBFX or Arm64Mnemonic.UBFIZ or Arm64Mnemonic.SBFIZ)
            || width==0 || Width(native.Op1Reg)!=width
            || native.Op0Kind!=Arm64OperandKind.Register || native.Op1Kind!=Arm64OperandKind.Register
            || native.Op2Kind!=Arm64OperandKind.Immediate || native.Op3Kind!=Arm64OperandKind.Immediate
            || native.Op2Imm<0 || native.Op2Imm>=bits || native.Op3Imm<1
            || native.Op3Imm>bits-native.Op2Imm)return null;
        var lsb=(int)native.Op2Imm;var count=(int)native.Op3Imm;
        var insert=native.Mnemonic is Arm64Mnemonic.UBFIZ or Arm64Mnemonic.SBFIZ;
        var sign=native.Mnemonic is Arm64Mnemonic.SBFX or Arm64Mnemonic.SBFIZ;
        var unsigned=width==4?types.SystemUInt32Type:types.SystemUInt64Type;
        var signed=width==4?types.SystemInt32Type:types.SystemInt64Type;
        var result=new List<Instruction>();
        Register Temp(string name)=>new(null,"BITFIELD_EXTRACT_"+name);
        void Emit(OpCode code,params IOperand[] args)=>result.Add(new(result.Count,code,args.ToList()){NativeArithmeticSize=width});
        var input=Temp("INPUT");Emit(OpCode.NumericConvert,input,unsigned,unsigned,Read(native.Op1Reg,width));
        IOperand value=input;
        if(!insert && lsb!=0)
        {
            var shifted=Temp("EXTRACT");Emit(OpCode.ShiftRightUnsigned,shifted,value,new Immediate(lsb));value=shifted;
        }
        var field=Temp("FIELD");
        Emit(OpCode.And,field,value,new Immediate(unchecked((long)(count==64?ulong.MaxValue:(1UL<<count)-1))));
        value=field;
        if(sign)
        {
            if(count<bits)
            {
                var high=Temp("HIGH");Emit(OpCode.ShiftLeft,high,value,new Immediate(bits-count));value=high;
            }
            var signedHigh=Temp("SIGNED");Emit(OpCode.NumericConvert,signedHigh,signed,unsigned,value);value=signedHigh;
            if(count<bits)
            {
                var extended=Temp("EXTENDED");Emit(OpCode.ShiftRight,extended,value,new Immediate(bits-count));value=extended;
            }
        }
        if(insert && lsb!=0)
        {
            var shifted=Temp("INSERT");Emit(OpCode.ShiftLeft,shifted,value,new Immediate(lsb));value=shifted;
        }
        var destination=Read(native.Op0Reg,width) is Register r?r:Temp("DISCARDED");
        Emit(OpCode.NumericConvert,destination,unsigned,sign?signed:unsigned,value);
        return result;
    }
}
