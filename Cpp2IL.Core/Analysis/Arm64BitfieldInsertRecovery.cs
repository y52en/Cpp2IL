using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// Preserve the old destination bits outside the exact inserted field.
// Unlike MOV/OR this is a read-modify-write; source and destination may alias.
public static class Arm64BitfieldInsertRecovery
{
    private static int Width(Arm64Register r)=>r switch {
        >=Arm64Register.W0 and <=Arm64Register.W31=>4,
        >=Arm64Register.X0 and <=Arm64Register.X31=>8,_=>0};
    private static IOperand Read(Arm64Register r,int width)
    {
        var number=(int)r-(int)(width==4?Arm64Register.W0:Arm64Register.X0);
        return number==31?new Immediate(0):new Register(null,"X"+number);
    }

    public static List<Instruction>? Lower(Arm64Instruction native,SystemTypesContext types)
    {
        var width=Width(native.Op0Reg);var bits=width*8;
        if(native.Mnemonic is not (Arm64Mnemonic.BFI or Arm64Mnemonic.BFXIL)
            || width==0 || Width(native.Op1Reg)!=width
            || native.Op0Kind!=Arm64OperandKind.Register || native.Op1Kind!=Arm64OperandKind.Register
            || native.Op2Kind!=Arm64OperandKind.Immediate || native.Op3Kind!=Arm64OperandKind.Immediate
            || native.Op2Imm<0 || native.Op2Imm>=bits || native.Op3Imm<1
            || native.Op3Imm>bits-native.Op2Imm)return null;
        var lsb=(int)native.Op2Imm;var count=(int)native.Op3Imm;
        var type=width==4?types.SystemUInt32Type:types.SystemUInt64Type;
        var low=count==64?ulong.MaxValue:(1UL<<count)-1;
        var insert=native.Mnemonic==Arm64Mnemonic.BFI;
        var mask=insert?low<<lsb:low;var domain=width==4?uint.MaxValue:ulong.MaxValue;
        var result=new List<Instruction>();
        Register Temp(string name)=>new(null,"BITFIELD_INSERT_"+name);
        void Emit(OpCode code,params IOperand[] args)=>result.Add(new(result.Count,code,args.ToList()){NativeArithmeticSize=width});
        var old=Temp("OLD");var source=Temp("SOURCE");
        Emit(OpCode.NumericConvert,old,type,type,Read(native.Op0Reg,width));
        Emit(OpCode.NumericConvert,source,type,type,Read(native.Op1Reg,width));
        var kept=Temp("KEPT");Emit(OpCode.And,kept,old,new Immediate(unchecked((long)(domain&~mask))));
        IOperand value=source;
        if(lsb!=0)
        {
            var shifted=Temp("SHIFTED");Emit(insert?OpCode.ShiftLeft:OpCode.ShiftRightUnsigned,shifted,source,new Immediate(lsb));
            value=shifted;
        }
        var field=Temp("FIELD");Emit(OpCode.And,field,value,new Immediate(unchecked((long)mask)));
        var merged=Temp("MERGED");Emit(OpCode.Or,merged,kept,field);
        var destination=Read(native.Op0Reg,width) is Register r?r:Temp("DISCARDED");
        Emit(OpCode.NumericConvert,destination,type,type,merged);
        return result;
    }
}
