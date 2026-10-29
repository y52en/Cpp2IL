using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;
public class Arm64ZeroBranchWidthTests
{
    [TestCase(0xb4000020u,8)] // CBZ X0,+4
    [TestCase(0xb5000020u,8)] // CBNZ X0,+4
    [TestCase(0x34000020u,4)] // CBZ W0,+4
    [TestCase(0x35000020u,4)] // CBNZ W0,+4
    public void PreserveDecodedReferenceOrLowWordComparisonWidth(uint word,int width)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var instruction=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        var lifted=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[instruction,lifted,new List<ulong>(),context]);
        Assert.That(lifted.Single(i=>i.OpCode==OpCode.CheckEqual).NativeComparisonSize,Is.EqualTo(width));
        Assert.That(lifted.Last().OpCode,Is.EqualTo(OpCode.ConditionalJump));
    }
}
