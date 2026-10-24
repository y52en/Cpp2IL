using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64CompareWidthTests
{
    [TestCase(0x6b01011fu,4)] // CMP W8,W1
    [TestCase(0xeb01011fu,8)] // CMP X8,X1
    [TestCase(0x7100051fu,4)] // CMP W8,#1
    [TestCase(0xf100051fu,8)] // CMP X8,#1
    [TestCase(0x6b010109u,4)] // SUBS W9,W8,W1
    [TestCase(0xeb010109u,8)] // SUBS X9,X8,X1
    public void FlagDifferenceRetainsDecodedArithmeticWidth(uint word,int width)
    {
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1d1e760,new(true,true,false)).Single();
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var method=new InjectedMethodAnalysisContext(types.SystemObjectType,"Test",types.SystemVoidType,MethodAttributes.Static,[]);
        var instructions=new List<Instruction>();var addresses=new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[native,instructions,addresses,method]);
        var flagDifference=instructions.Single(i=>i.OpCode==OpCode.Subtract
            && i.Destination is Register {Name:"TEMP1"});
        Assert.That(flagDifference.NativeArithmeticSize,Is.EqualTo(width));
        Assert.That(instructions.Any(i=>i.OpCode==OpCode.CheckLess && i.UnsignedComparison),Is.True);
    }
}
