using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64MultiplyTests
{
    static IEnumerable<object[]> Cases()
    {
        foreach(var wide in new[]{false,true})
        foreach(var form in new[]{"mul","madd","msub","mneg"})yield return [wide,form];
        foreach(var form in new[]{"smull","umull","smaddl","umaddl","smsubl","umsubl","smnegl","umnegl"})yield return [true,form];
    }
    static Arm64Instruction Native(bool wide,string form)
    {
        var signed=form.StartsWith("sm");var unsigned=form.StartsWith("um");
        var widening=signed || unsigned;
        var subtract=form.Contains("sub") || form.Contains("neg");
        var accumulate=form.Contains("add") || form.Contains("sub");
        uint word=(wide?0x9b000000u:0x1b000000u)|(widening?(signed?0x00200000u:0x00a00000u):0)
            |22u<<16|(subtract?0x8000u:0)|(accumulate?19u:31u)<<10|19u<<5|10u;
        return Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
    }
    [TestCaseSource(nameof(Cases))]
    public void WidenBeforeMultiplyAndPreserveNativeModuloAndAccumulateOrder(bool wide,string form)
    {
        var native=Native(wide,form);
        Assert.That(native.Mnemonic.ToString().ToLowerInvariant(),Is.EqualTo(form));
        var lowered=Arm64MultiplyRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes);
        Assert.That(lowered,Is.Not.Null);
        var widening=form.StartsWith("sm") || form.StartsWith("um");
        var signed=form.StartsWith("sm");
        var mask=(BigInteger.One<<(wide?64:32))-1;
        foreach(var a in new[]{0UL,1UL,0x80000000UL,uint.MaxValue,0x8000000000000000UL,ulong.MaxValue})
        foreach(var b in new[]{0UL,3UL,381774871UL,uint.MaxValue,ulong.MaxValue})
        {
            BigInteger left=widening?(signed?(BigInteger)(int)a:(uint)a):wide?(BigInteger)a:(uint)a;
            BigInteger right=widening?(signed?(BigInteger)(int)b:(uint)b):wide?(BigInteger)b:(uint)b;
            var product=left*right;
            var addend=wide?(BigInteger)a:(uint)a;
            var expected=form.Contains("add")?addend+product:form.Contains("sub")?addend-product
                :form.Contains("neg")?-product:product;
            Assert.That(Arm64ShiftedLogicalTests.Execute(lowered!,a,b),Is.EqualTo((ulong)(expected&mask)),native.ToString());
        }
    }
    [Test]
    public void FloatingMultiplyDoesNotAcquireAnIntegerContract()
    {
        var native=Disassembler.Disassemble(BitConverter.GetBytes(0x1e220820u),0x1000,new(true,true,false)).Single();
        Assert.That(Arm64MultiplyRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes),Is.Null);
    }
    [TestCase("madd")]
    [TestCase("msub")]
    [TestCase("umaddl")]
    [TestCase("smaddl")]
    public void FrontendPreservesRawAffineGraphAndDefersScalarConversionsUntilEmission(string form)
    {
        var app=TestGameLoader.LoadSimple2019Game();var native=Native(true,form);
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"AffineMultiply",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var actual=new List<Instruction>();var addresses=new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[native,actual,addresses,method]);
        Assert.That(actual.Count,Is.EqualTo(2));
        Assert.That(actual[0].OpCode,Is.EqualTo(OpCode.Multiply));
        Assert.That(actual[0].NativeArithmeticSize,Is.EqualTo(8));
        Assert.That(actual[0].NativeMultiplyInputSize,Is.EqualTo(form is "madd" or "msub"?8:4));
        Assert.That(actual[0].NativeMultiplySigned,Is.EqualTo(form=="smaddl"));
        Assert.That(actual[1].OpCode,Is.EqualTo(form=="msub"?OpCode.Subtract:OpCode.Add));
        Assert.That(((Register)actual[1].Operands[1]).Name,Is.EqualTo("X19"));
        Assert.That(actual[1].NativeArithmeticSize,Is.EqualTo(8));
    }
}
