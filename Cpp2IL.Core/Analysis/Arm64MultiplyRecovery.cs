using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// Integer multiply families have explicit native input/output widths. In
// particular UMULL/SMULL do NOT multiply two I4 values then widen the product.
public static class Arm64MultiplyRecovery
{
    public readonly record struct Contract(int OutputWidth,int InputWidth,bool Signed);
    public static Contract? Describe(Arm64Instruction n)
    {
        var signed=n.Mnemonic is Arm64Mnemonic.SMULL or Arm64Mnemonic.SMADDL or Arm64Mnemonic.SMSUBL or Arm64Mnemonic.SMNEGL;
        var widening=signed || n.Mnemonic is Arm64Mnemonic.UMULL or Arm64Mnemonic.UMADDL or Arm64Mnemonic.UMSUBL or Arm64Mnemonic.UMNEGL;
        var accumulate=n.Mnemonic is Arm64Mnemonic.MADD or Arm64Mnemonic.MSUB or Arm64Mnemonic.SMADDL
            or Arm64Mnemonic.UMADDL or Arm64Mnemonic.SMSUBL or Arm64Mnemonic.UMSUBL;
        var negate=n.Mnemonic is Arm64Mnemonic.MNEG or Arm64Mnemonic.SMNEGL or Arm64Mnemonic.UMNEGL;
        if(!accumulate && !negate && n.Mnemonic is not (Arm64Mnemonic.MUL or Arm64Mnemonic.SMULL or Arm64Mnemonic.UMULL))return null;
        var width=Width(n.Op0Reg);var input=widening?4:width;
        if(width==0 || widening && width!=8 || Width(n.Op1Reg)!=input || Width(n.Op2Reg)!=input
            || accumulate && Width(n.Op3Reg)!=width)return null;
        return new(width,input,signed);
    }
    static int Width(Arm64Register r)=>r switch
    {
        >=Arm64Register.W0 and <=Arm64Register.W31=>4,
        >=Arm64Register.X0 and <=Arm64Register.X31=>8,_=>0
    };
    static IOperand Read(Arm64Register r)
    {
        var n=(int)r-(int)(Width(r)==4?Arm64Register.W0:Arm64Register.X0);
        return n==31?new Immediate(0):new Register(null,"X"+n);
    }
    public static List<Instruction>? Lower(Arm64Instruction n,SystemTypesContext t)
    {
        var signed=n.Mnemonic is Arm64Mnemonic.SMULL or Arm64Mnemonic.SMADDL
            or Arm64Mnemonic.SMSUBL or Arm64Mnemonic.SMNEGL;
        var widening=signed || n.Mnemonic is Arm64Mnemonic.UMULL or Arm64Mnemonic.UMADDL
            or Arm64Mnemonic.UMSUBL or Arm64Mnemonic.UMNEGL;
        var accumulate=n.Mnemonic is Arm64Mnemonic.MADD or Arm64Mnemonic.MSUB
            or Arm64Mnemonic.SMADDL or Arm64Mnemonic.UMADDL or Arm64Mnemonic.SMSUBL or Arm64Mnemonic.UMSUBL;
        var negate=n.Mnemonic is Arm64Mnemonic.MNEG or Arm64Mnemonic.SMNEGL or Arm64Mnemonic.UMNEGL;
        if(!accumulate && !negate && n.Mnemonic is not (Arm64Mnemonic.MUL or Arm64Mnemonic.SMULL or Arm64Mnemonic.UMULL))return null;
        var width=Width(n.Op0Reg);var inputWidth=widening?4:width;
        if(width==0 || widening && width!=8 || Width(n.Op1Reg)!=inputWidth || Width(n.Op2Reg)!=inputWidth
            || accumulate && Width(n.Op3Reg)!=width)return null;
        var inputType=inputWidth==4?(signed?t.SystemInt32Type:t.SystemUInt32Type)
            :(signed?t.SystemInt64Type:t.SystemUInt64Type);
        var operationType=width==4?t.SystemUInt32Type:signed?t.SystemInt64Type:t.SystemUInt64Type;
        var outputType=width==4?t.SystemUInt32Type:t.SystemUInt64Type;
        var result=new List<Instruction>();
        Register Temp(string name)=>new(null,"MULTIPLY_"+name);
        void Emit(OpCode op,params IOperand[] values)=>result.Add(new(result.Count,op,[..values]){NativeArithmeticSize=width});
        Register Input(Arm64Register reg,string name)
        {
            var narrow=Temp(name+"_INPUT");Emit(OpCode.NumericConvert,narrow,inputType,inputType,Read(reg));
            if(!widening)return narrow;
            var wide=Temp(name+"_WIDE");Emit(OpCode.NumericConvert,wide,operationType,inputType,narrow);return wide;
        }
        var left=Input(n.Op1Reg,"LEFT");var right=Input(n.Op2Reg,"RIGHT");
        var product=Temp("PRODUCT");Emit(OpCode.Multiply,product,left,right);
        IOperand value=product;
        if(accumulate)
        {
            var addend=Temp("ADDEND");Emit(OpCode.NumericConvert,addend,operationType,operationType,Read(n.Op3Reg));
            var combined=Temp("COMBINED");
            var subtract=n.Mnemonic is Arm64Mnemonic.MSUB or Arm64Mnemonic.SMSUBL or Arm64Mnemonic.UMSUBL;
            Emit(subtract?OpCode.Subtract:OpCode.Add,combined,addend,product);value=combined;
        }
        else if(negate){var negative=Temp("NEGATED");Emit(OpCode.Negate,negative,product);value=negative;}
        Emit(OpCode.NumericConvert,Read(n.Op0Reg) is Register destination?destination:Temp("DISCARDED"),outputType,operationType,value);
        return result;
    }
}
