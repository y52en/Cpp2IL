using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ShiftedLogicalTests
{
    static IEnumerable<object[]> Cases()
    {
        foreach(var wide in new[]{false,true})
        foreach(var operation in Enumerable.Range(0,4))
        foreach(var invert in new[]{false,true})
        foreach(var shift in Enumerable.Range(0,4))yield return [wide,operation,invert,shift];
    }

    static Arm64Instruction Native(bool wide,int operation,bool invert,int kind,int amount,bool alias=false)
    {
        uint word=0x0a000000u|(wide?0x80000000u:0)|((uint)operation<<29)|((uint)kind<<22)
            |(invert?1u<<21:0)|(22u<<16)|((uint)amount<<10)|((alias?10u:19u)<<5)|10u;
        return Disassembler.Disassemble(BitConverter.GetBytes(word),0x1d167d4,new(true,true,false)).Single();
    }

    // Small CIL integer-stack evaluator: the independent expected expression
    // below uses unsigned ARM bit-vector shifts, while lowered SHR is signed
    // and must be corrected by its emitted width mask.
    internal static ulong Execute(List<Instruction> instructions,ulong a,ulong b,bool alias=false)
    {
        var values=new Dictionary<string,(ulong Bits,int Width)>{{alias?"X10":"X19",(a,8)},{"X22",(b,8)}};
        (ulong Bits,int Width) Read(IOperand operand)=>operand switch
        {
            Register register=>values[register.Name],Immediate value=>(unchecked((ulong)value.Value),value.Value is >=int.MinValue and <=int.MaxValue?4:8),
            _=>throw new InvalidOperationException("unmodeled numeric operand"),
        };
        foreach(var i in instructions)
        {
            var destination=((Register)i.Operands[0]).Name;
            if(i.OpCode==OpCode.NumericConvert)
            {
                var value=Read(i.Operands[3]);var type=((TypeAnalysisContext)i.Operands[1]).FullName;
                values[destination]=type switch
                {
                    "System.UInt32" or "System.Int32"=>((uint)value.Bits,4),
                    "System.UInt64"=>(value.Width==4?(uint)value.Bits:value.Bits,8),
                    "System.Int64"=>(value.Width==4?unchecked((ulong)(long)(int)value.Bits):value.Bits,8),
                    _=>throw new InvalidOperationException(type),
                };continue;
            }
            var left=Read(i.Operands[1]);var right=i.Operands.Count==3?Read(i.Operands[2]).Bits:0;
            var result=i.OpCode switch
            {
                OpCode.ShiftLeft=>left.Bits<<(int)right,
                OpCode.ShiftRight=>left.Width==4?unchecked((ulong)((int)left.Bits>>(int)right))
                    :unchecked((ulong)((long)left.Bits>>(int)right)),
                OpCode.ShiftRightUnsigned=>left.Width==4?(uint)left.Bits>>(int)right:left.Bits>>(int)right,
                OpCode.And=>left.Bits&right,OpCode.Or=>left.Bits|right,OpCode.Xor=>left.Bits^right,
                OpCode.Add=>unchecked(left.Bits+right),OpCode.Subtract=>unchecked(left.Bits-right),
                OpCode.Multiply=>unchecked(left.Bits*right),OpCode.Negate=>unchecked(0UL-left.Bits),
                OpCode.Not=>~left.Bits,_=>throw new InvalidOperationException(i.OpCode.ToString()),
            };
            values[destination]=(left.Width==4?(uint)result:result,left.Width);
        }
        return values["X10"].Bits;
    }

    static ulong Expected(ulong a,ulong b,bool wide,int op,bool invert,int kind,int amount)
    {
        var bits=wide?64:32;var mask=wide?ulong.MaxValue:uint.MaxValue;a&=mask;b&=mask;
        var shifted=kind switch
        {
            0=>(b<<amount)&mask,1=>b>>amount,
            2=>wide?unchecked((ulong)((long)b>>amount))&mask:unchecked((uint)((int)b>>amount)),
            3=>((b>>amount)|(b<<(bits-amount)))&mask,_=>throw new ArgumentException(),
        };
        if(invert)shifted=~shifted&mask;
        return (op switch{0 or 3=>a&shifted,1=>a|shifted,2=>a^shifted,_=>throw new ArgumentException()})&mask;
    }

    [TestCaseSource(nameof(Cases))]
    public void EveryLogicalShiftKindPreservesWidthHighBitsInversionAndOperandOrder(bool wide,int op,bool invert,int kind)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var inputs=new[]{0UL,1UL,0x80000000UL,0xffffffffUL,0x8000000000000000UL,ulong.MaxValue,0x1234567889abcdefUL};
        foreach(var amount in new[]{1,wide?63:31})
        {
            var lowered=Arm64ShiftedLogicalRecovery.Lower(Native(wide,op,invert,kind,amount),types);
            Assert.That(lowered,Is.Not.Null);
            foreach(var a in inputs)foreach(var b in inputs)
                Assert.That(Execute(lowered!,a,b),Is.EqualTo(Expected(a,b,wide,op,invert,kind,amount)));
        }
    }

    [Test]
    public void OriginalCrcEncodingRetainsRightShiftBeforeXorAndBothRegisterReadsBeforeWrite()
    {
        var native=Disassembler.Disassemble(new byte[]{0x6a,0x06,0x56,0x4a},0x1d167d4,new(true,true,false)).Single();
        var lowered=Arm64ShiftedLogicalRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(lowered.Any(i=>i.OpCode==OpCode.ShiftRight),Is.True);
        Assert.That(Execute(lowered,0xedb88320,3),Is.EqualTo(0xedb88321UL));
        var alias=Arm64ShiftedLogicalRecovery.Lower(Native(false,2,false,1,1,true),TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(Execute(alias,0xedb88320,3,true),Is.EqualTo(0xedb88321UL));
    }

    [Test]
    public void UnshiftedInstructionsStayOnExistingLiftingPath()
        =>Assert.That(Arm64ShiftedLogicalRecovery.Lower(Native(false,2,false,0,0),TestGameLoader.LoadSimple2019Game().SystemTypes),Is.Null);

    [TestCase(false,"System.UInt32")]
    [TestCase(true,"System.UInt64")]
    public void InputContractUsesTheNativeReadWidthNotTheNormalizedXRegisterName(bool wide,string expected)
    {
        var lowered=Arm64ShiftedLogicalRecovery.Lower(Native(wide,2,false,1,1),TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(lowered.Take(2).Select(i=>((TypeAnalysisContext)i.Operands[2]).FullName),Is.All.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RealFrontendUsesTheShiftedContractAndPreservesFlagEmission(bool flags)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"ShiftedLogical",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Native(false,flags?3:2,false,1,1);
        var lowered=Arm64ShiftedLogicalRecovery.Lower(native,app.SystemTypes)!;
        var actual=new List<Instruction>();var addresses=new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[native,actual,addresses,method]);
        Assert.That(actual.Take(lowered.Count).Select(i=>i.OpCode),Is.EqualTo(lowered.Select(i=>i.OpCode)));
        Assert.That(actual.Count>lowered.Count,Is.EqualTo(flags));
        Assert.That(addresses.All(a=>a==0x1d167d4),Is.True);
    }
}
