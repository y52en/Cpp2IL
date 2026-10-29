using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64IntegerExtendTests
{
    [TestCase(0x13001c20u,"System.SByte","System.UInt32")]
    [TestCase(0x13003c20u,"System.Int16","System.UInt32")]
    [TestCase(0x93401c20u,"System.SByte","System.Int64")]
    [TestCase(0x93403c20u,"System.Int16","System.Int64")]
    [TestCase(0x93407c20u,"System.Int32","System.Int64")]
    [TestCase(0x53001c20u,"System.Byte","System.UInt32")]
    [TestCase(0x53003c20u,"System.UInt16","System.UInt32")]
    public void ActualDecodedExtensionNarrowsThenExtendsWithNoCopy(uint word,string narrow,string target)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        var instructions=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),new object[]{native,instructions,new List<ulong>(),caller});
        Assert.That(instructions.Count,Is.EqualTo(2));
        Assert.That(instructions.All(i=>i.OpCode==OpCode.NumericConvert),Is.True);
        Assert.That(((TypeAnalysisContext)instructions[0].Operands[1]).FullName,Is.EqualTo(narrow));
        Assert.That(((TypeAnalysisContext)instructions[1].Operands[1]).FullName,Is.EqualTo(target));
        Assert.That(instructions[0].NativeIntegerSourceView,Is.True);
        Assert.That(instructions[1].NativeIntegerSourceView,Is.False);
        Assert.That(((TypeAnalysisContext)instructions[0].Operands[2]).FullName,Is.EqualTo("System.UInt64"));
        Assert.That(instructions.All(i=>i.NativeRegisterCopySize==0),Is.True);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void LowBitViewDoesNotRetagWholeUnknownOrMetadataTypedProducer(bool known)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var source=new LocalVariable("whole",new Register(null,"X1"),known?types.SystemInt64Type:null);
        var narrowed=new LocalVariable("low",new Register(null,"temp"));
        var result=new LocalVariable("result",new Register(null,"X0"));
        var first=new Instruction(0,OpCode.NumericConvert,narrowed,types.SystemInt32Type,types.SystemUInt64Type,source)
            {NativeIntegerSourceView=true};
        var second=new Instruction(1,OpCode.NumericConvert,result,types.SystemInt64Type,types.SystemInt32Type,narrowed);
        var method=new InjectedMethodAnalysisContext(types.SystemObjectType,"Sxtw",types.SystemInt64Type,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([first,second,new(2,OpCode.Return,result)]);
        method.Locals=[source,narrowed,result];method.ParameterLocals=[];method.AnalysisWarnings=[];
        LocalVariables.ResolveTypesAndFields(method);SsaSimplifier.Run(method);
        Assert.That(source.Type,Is.SameAs(known?types.SystemInt64Type:null));
        Assert.That(narrowed.Type,Is.SameAs(types.SystemInt32Type));
        Assert.That(result.Type,Is.SameAs(types.SystemInt64Type));
        Assert.That(first.OpCode,Is.EqualTo(OpCode.NumericConvert));
        Assert.That(second.OpCode,Is.EqualTo(OpCode.NumericConvert));
    }
}
