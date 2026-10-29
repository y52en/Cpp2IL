using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ScalarTestFlagsTests
{
    private static Arm64Instruction Decode(uint word)=>Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
    [TestCase(false,0,0)] [TestCase(false,0,1)] [TestCase(false,0,31)]
    [TestCase(false,4,0)] [TestCase(false,4,1)] [TestCase(false,4,31)]
    [TestCase(true,0,0)] [TestCase(true,0,1)] [TestCase(true,0,31)]
    [TestCase(true,4,0)] [TestCase(true,4,1)] [TestCase(true,4,31)]
    public void ExtendedAddsFlagsAndAliasedResultMatchIndependentArithmetic(bool signed,int shift,int destination)
    {
        var word=0xab214000u|(signed?0x8000u:0)|((uint)shift<<10)|(uint)destination;
        var code=Arm64ScalarTestFlags.Lower(Decode(word),TestGameLoader.LoadSimple2019Game().SystemTypes);
        Assert.That(code,Is.Not.Null);
        var values=new[]{0UL,1UL,0x7fffffffUL,0x80000000UL,0xffffffffUL,
            0x7fffffffffffffffUL,0x8000000000000000UL,ulong.MaxValue,0xdeadbeef00000003UL};
        var modulus=BigInteger.One<<64;var mask=modulus-1;var sign=BigInteger.One<<63;
        foreach(var a in values)foreach(var b in values)
        {
            var extended=signed?new BigInteger(unchecked((int)b)):new BigInteger(unchecked((uint)b));
            var right=(extended<<shift)&mask;var sum=(BigInteger)a+right;var result=sum&mask;
            var negative=(result&sign)!=0;var zero=result==0;var carry=sum>=modulus;
            var overflow=(((BigInteger)a^result)&(right^result)&sign)!=0;
            var expected=(negative?8:0)|(zero?4:0)|(carry?2:0)|(overflow?1:0);
            Assert.That(Execute(code!,a,b,out var registers),Is.EqualTo(expected));
            if(destination!=31)Assert.That(registers["X"+destination],Is.EqualTo((ulong)result));
            else
            {
                Assert.That(registers["X0"],Is.EqualTo(a));
                Assert.That(registers["X1"],Is.EqualTo(b));
            }
        }
    }

    [Test]
    public void ExtendedByteInputIsNotMistakenForAnUnmodifiedWordRegister()
    {
        var native=Decode(0x2b21001fu); // CMN W0,W1,UXTB
        Assert.That(native.Mnemonic.ToString(),Is.AnyOf("CMN","ADDS"));
        Assert.That(Arm64ScalarTestFlags.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes),Is.Null);
    }
    private static IEnumerable<object[]> Cases()
    {
        foreach(var wide in new[]{false,true})
        {
            var sf=wide?0x80000000u:0;
            yield return [0x3100001fu|sf,"add",0,0,0];
            yield return [0x3100041fu|sf,"add",1,0,0];
            yield return [0x313ffc1fu|sf,"add",4095,0,0];
            yield return [0x3140041fu|sf,"add",1,0,12];
            yield return [0x2b01001fu|sf,"add",-1,0,0];
            yield return [0x31000400u|sf,"add",1,0,0]; // ADDS W/X0,W/X0,#1
            yield return [0x2b010001u|sf,"add",-1,0,0]; // ADDS W/X1,W/X0,W/X1
            foreach(var kind in new[]{0,1,2})
            foreach(var amount in new[]{1,wide?63:31})
                yield return [0x2b01001fu|sf|((uint)kind<<22)|((uint)amount<<10),"add",-1,kind,amount];
            yield return [0x6a01001fu|sf,"and",-1,0,0];
            yield return [0x6a010000u|sf,"and",-1,0,0]; // ANDS W/X0,W/X0,W/X1
            foreach(var kind in new[]{0,1,2})
                yield return [0x6a01001fu|sf|((uint)kind<<22)|(1u<<10),"and",-1,kind,1];
            yield return [0x6a01001fu|sf|(3u<<22)|(1u<<10),"and",-1,3,1]; // ROR
            // TST W0,#0x80000000 / TST X0,#0x8000000000000000
            yield return [wide?0xf241001fu:0x7201001fu,"mask",0,0,0];
        }
    }

    [TestCaseSource(nameof(Cases))]
    public void ActualDecodedFlagsAgreeWithIndependentUnboundedIntegerArithmetic(uint word,string operation,int immediate,int shiftKind,int amount)
    {
        var app=TestGameLoader.LoadSimple2019Game();var native=Decode(word);
        Assert.That(native.Mnemonic.ToString(),operation=="add"?Is.AnyOf("CMN","ADDS"):Is.AnyOf("TST","ANDS"));
        var code=Arm64ScalarTestFlags.Lower(native,app.SystemTypes);
        Assert.That(code,Is.Not.Null,native.ToString());
        var width=(word&0x80000000)!=0?8:4;var bits=width*8;
        var modulus=BigInteger.One<<bits;var mask=modulus-1;var sign=BigInteger.One<<(bits-1);
        BigInteger Signed(BigInteger value)=>value>=sign?value-modulus:value;
        var values=new[]{0UL,1UL,2UL,0x7fffffffUL,0x80000000UL,0xffffffffUL,
            0x7fffffffffffffffUL,0x8000000000000000UL,ulong.MaxValue,0x1234567889abcdefUL};
        foreach(var a in values)foreach(var b in values)
        {
            BigInteger left=(BigInteger)a&mask;
            BigInteger right=operation=="mask"?sign:immediate>=0?immediate:(BigInteger)b&mask;
            right=shiftKind switch{0=>(right<<amount)&mask,1=>right>>amount,2=>(Signed(right)>>amount)&mask,
                3=>((right>>amount)|(right<<(bits-amount)))&mask,_=>throw new ArgumentException()};
            var unbounded=left+right;var result=operation=="add"?unbounded&mask:left&right;
            var signedSum=Signed(left)+Signed(right);
            var expected=(result>=sign?8:0)|(result.IsZero?4:0)
                |(operation=="add"&&unbounded>=modulus?2:0)
                |(operation=="add"&&(signedSum< -sign || signedSum>=sign)?1:0);
            Assert.That(Execute(code!,a,b,out var registers),Is.EqualTo(expected),native+" a="+a.ToString("X")+" b="+b.ToString("X"));
            var destination=native.Op0Reg.ToString();
            if(native.Mnemonic.ToString()is "ADDS"or "ANDS" && destination is not ("X31"or "W31"))
                Assert.That(registers["X"+destination[1..]],Is.EqualTo((ulong)result),"architectural result/upper W bits");
            else
            {
                Assert.That(registers["X0"],Is.EqualTo(a),"discarded destination must not overwrite its source");
                Assert.That(registers["X1"],Is.EqualTo(b));
            }
        }
    }

    private static int Execute(List<Instruction> code,ulong a,ulong b,out Dictionary<string,ulong> registers)
    {
        var values=new Dictionary<string,(ulong Bits,int Width)>{{"X0",(a,8)},{"X1",(b,8)}};
        (ulong Bits,int Width) Read(IOperand operand)=>operand switch
        {
            Register r=>values[r.Name],Immediate i=>(unchecked((ulong)i.Value),i.Value is >=int.MinValue and <=int.MaxValue?4:8),
            _=>throw new InvalidOperationException(operand.ToString()),
        };
        foreach(var instruction in code)
        {
            var destination=((Register)instruction.Operands[0]).Name;
            if(instruction.OpCode==OpCode.NumericConvert)
            {
                var v=Read(instruction.Operands[3]);var type=((TypeAnalysisContext)instruction.Operands[1]).FullName;
                values[destination]=type switch
                {
                    "System.UInt32" or "System.Int32"=>((uint)v.Bits,4),
                    "System.UInt64"=>(v.Width==4?(uint)v.Bits:v.Bits,8),
                    "System.Int64"=>(v.Width==4?unchecked((ulong)(long)(int)v.Bits):v.Bits,8),
                    _=>throw new InvalidOperationException(type),
                };continue;
            }
            var left=Read(instruction.Operands[1]);
            var right=instruction.Operands.Count==3?Read(instruction.Operands[2]):(Bits:0UL,Width:4);
            if(instruction.OpCode is OpCode.CheckEqual or OpCode.CheckLess)
            {
                var yes=instruction.OpCode==OpCode.CheckEqual?left.Bits==right.Bits:instruction.UnsignedComparison
                    ?left.Bits<right.Bits:left.Width==4?(int)left.Bits<(int)right.Bits:(long)left.Bits<(long)right.Bits;
                values[destination]=(yes?1UL:0UL,4);continue;
            }
            var result=instruction.OpCode switch
            {
                OpCode.Move=>left.Bits,OpCode.Add=>unchecked(left.Bits+right.Bits),
                OpCode.And=>left.Bits&right.Bits,OpCode.Xor=>left.Bits^right.Bits,OpCode.Or=>left.Bits|right.Bits,
                OpCode.ShiftLeft=>left.Bits<<(int)right.Bits,
                OpCode.ShiftRightUnsigned=>left.Width==4?(uint)left.Bits>>(int)right.Bits:left.Bits>>(int)right.Bits,
                OpCode.ShiftRight=>left.Width==4?unchecked((uint)((int)left.Bits>>(int)right.Bits)):unchecked((ulong)((long)left.Bits>>(int)right.Bits)),
                _=>throw new InvalidOperationException(instruction.OpCode.ToString()),
            };
            values[destination]=(left.Width==4?(uint)result:result,left.Width);
        }
        registers=values.ToDictionary(v=>v.Key,v=>v.Value.Bits);
        return (int)(values["N"].Bits<<3|values["Z"].Bits<<2|values["C"].Bits<<1|values["V"].Bits);
    }

    [TestCase(0x3100041fu)]
    [TestCase(0xb100041fu)]
    [TestCase(0x7201001fu)]
    public void RealFrontendRetainsAllFlagAndInputViewContracts(uint word)
    {
        var app=TestGameLoader.LoadSimple2019Game();var native=Decode(word);
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Flags",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var actual=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!.SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[native,actual,new List<ulong>(),method]);
        var expected=Arm64ScalarTestFlags.Lower(native,app.SystemTypes)!;
        Assert.That(actual.Select(i=>(i.OpCode,i.NativeArithmeticSize,i.NativeComparisonSize,i.NativeIntegerSourceView,i.UnsignedComparison)),
            Is.EqualTo(expected.Select(i=>(i.OpCode,i.NativeArithmeticSize,i.NativeComparisonSize,i.NativeIntegerSourceView,i.UnsignedComparison))));
    }
}
