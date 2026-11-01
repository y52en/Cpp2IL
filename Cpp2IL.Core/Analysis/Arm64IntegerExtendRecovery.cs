using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// SXTB/SXTH/SXTW and UXTB/UXTH are bit conversions, NEVER register copies.
// Narrow first, then preserve the destination register's W/X extension rule.
public static class Arm64IntegerExtendRecovery
{
    public static List<Instruction>? Lower(Arm64Instruction native,SystemTypesContext types)
    {
        var wide=native.Op0Reg is >=Arm64Register.X0 and <=Arm64Register.X31;
        var word=native.Op0Reg is >=Arm64Register.W0 and <=Arm64Register.W31;
        if(native.Op0Kind!=Arm64OperandKind.Register || native.Op1Kind!=Arm64OperandKind.Register
            || native.Op1Reg is not (>=Arm64Register.W0 and <=Arm64Register.W31 or >=Arm64Register.X0 and <=Arm64Register.X31)
            || !wide && !word)return null;
        TypeAnalysisContext? narrow=native.Mnemonic switch
        {
            Arm64Mnemonic.SXTB=>types.SystemSByteType,
            Arm64Mnemonic.SXTH=>types.SystemInt16Type,
            Arm64Mnemonic.SXTW when wide=>types.SystemInt32Type,
            Arm64Mnemonic.UXTB when word=>types.SystemByteType,
            Arm64Mnemonic.UXTH when word=>types.SystemUInt16Type,
            _=>null,
        };
        if(narrow==null)return null;
        var signed=native.Mnemonic is Arm64Mnemonic.SXTB or Arm64Mnemonic.SXTH or Arm64Mnemonic.SXTW;
        var target=wide?(signed?types.SystemInt64Type:types.SystemUInt64Type):types.SystemUInt32Type;
        IOperand Read(Arm64Register register,bool isWide)
        {
            var number=(int)register-(int)(isWide?Arm64Register.X0:Arm64Register.W0);
            return number==31?new Immediate(0):new Register(null,"X"+number);
        }
        if(Read(native.Op0Reg,wide) is not Register destination)
            return [new(0,OpCode.Nop)];
        var temporary=new Register(null,"INTEGER_EXTEND_NARROW");
        var sourceWide=native.Op1Reg is >=Arm64Register.X0 and <=Arm64Register.X31;
        return [new(0,OpCode.NumericConvert,temporary,narrow,types.SystemUInt64Type,Read(native.Op1Reg,sourceWide))
                {NativeIntegerSourceView=true},
            new(1,OpCode.NumericConvert,destination,target,narrow,temporary)];
    }
}
