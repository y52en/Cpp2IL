using System.Collections.Generic;
using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class ComparisonWidthRecoveryTests
{
    private static LocalVariable V(string name)=>new(name,new Register(null,name));

    [TestCase(4,false,4)]
    [TestCase(8,false,8)]
    [TestCase(4,true,4)]
    [TestCase(8,true,8)]
    [TestCase(0,false,0)]
    [TestCase(2,false,0)]
    public void EqualityAndNotCarryOnlyTheOriginatingNativeWidth(int width,bool invert,int expected)
    {
        var a=V("a");var b=V("b");var difference=V("difference");var zero=V("zero");var condition=V("condition");
        var subtract=new Instruction(0,OpCode.Subtract,difference,a,b){NativeArithmeticSize=width};
        var flag=new Instruction(1,OpCode.CheckEqual,zero,difference,new Immediate(0));
        var instructions=new List<Instruction>{subtract,flag};
        if(invert)instructions.Add(new(2,OpCode.Not,condition,zero));
        else condition=zero;
        var yes=new Instruction(5,OpCode.Return);var no=new Instruction(4,OpCode.Return);
        instructions.Add(new(3,OpCode.ConditionalJump,yes,condition));instructions.Add(no);instructions.Add(yes);
        var graph=new ISILControlFlowGraph(instructions);
        var unsigned=flag.UnsignedComparison;
        FlagConditionRecovery.Run(graph);
        var recovered=invert?instructions[2]:flag;
        Assert.That(recovered.NativeComparisonSize,Is.EqualTo(expected));
        Assert.That(recovered.OpCode,Is.EqualTo(invert?OpCode.CheckNotEqual:OpCode.CheckEqual));
        Assert.That(recovered.Operands[1],Is.SameAs(a));Assert.That(recovered.Operands[2],Is.SameAs(b));
        Assert.That(flag.UnsignedComparison,Is.EqualTo(unsigned));
    }

    [TestCase("valid",4)]
    [TestCase("wide-operation",8)]
    [TestCase("conflicting",0)]
    [TestCase("different-input",0)]
    [TestCase("ambiguous",0)]
    [TestCase("unknown",0)]
    public void WidthProofRejectsConflictsAndDoesNotUseInputProducerWidths(string shape,int expected)
    {
        var a=V("a");var b=V("b");var other=V("other");var difference=V("difference");var zero=V("zero");
        var subtract=new Instruction(0,OpCode.Subtract,difference,a,shape=="different-input"?other:b)
            {NativeArithmeticSize=shape=="wide-operation"?8:shape=="unknown"?0:4};
        var flag=new Instruction(1,OpCode.CheckEqual,zero,difference,new Immediate(0))
            {NativeComparisonSize=shape=="conflicting"?8:0};
        var definitions=new Dictionary<LocalVariable,Instruction>{{difference,subtract},{zero,flag},
            {a,new(2,OpCode.Add,a,new Immediate(1),new Immediate(2)){NativeArithmeticSize=4}}};
        var ambiguous=new HashSet<LocalVariable>();if(shape=="ambiguous")ambiguous.Add(difference);
        Assert.That(FlagConditionRecovery.ProveComparisonSize(zero,definitions,ambiguous,a,b),Is.EqualTo(expected));
        Assert.That(subtract.Operands[1],Is.SameAs(a));Assert.That(flag.OpCode,Is.EqualTo(OpCode.CheckEqual));
    }

    [TestCase(0x6b01001fu,4)] // CMP W0,W1
    [TestCase(0xeb01001fu,8)] // CMP X0,X1
    [TestCase(0x6b010002u,4)] // SUBS W2,W0,W1
    [TestCase(0xeb010002u,8)] // SUBS X2,X0,X1
    public void ActualArmDecoderPreservesAllIntegerFlagComparisonWidths(uint word,int expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        Assert.That(native.Mnemonic.ToString(),Is.AnyOf("CMP","SUBS"));
        var instructions=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),new object[]{native,instructions,new List<ulong>(),caller});
        var comparisons=instructions.Where(i=>i.OpCode is OpCode.CheckLess or OpCode.CheckEqual).ToArray();
        Assert.That(comparisons.Length,Is.EqualTo(4));
        Assert.That(comparisons.All(i=>i.NativeComparisonSize==expected),Is.True);
        Assert.That(comparisons[0].UnsignedComparison,Is.True);
        Assert.That(comparisons.Skip(1).All(i=>!i.UnsignedComparison),Is.True);
    }
}
