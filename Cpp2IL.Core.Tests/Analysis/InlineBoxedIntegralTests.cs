using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlineBoxedIntegralTests
{
    [TestCase("valid",true)]
    [TestCase("peer",false)]
    [TestCase("incomplete",false)]
    [TestCase("native-store",false)]
    [TestCase("native-base",false)]
    [TestCase("native-destination",false)]
    [TestCase("ir-offset",false)]
    [TestCase("ir-width",false)]
    [TestCase("ir-index",false)]
    [TestCase("extra-use",false)]
    [TestCase("static",false)]
    [TestCase("arguments",false)]
    [TestCase("return-type",false)]
    [TestCase("field-offset",false)]
    [TestCase("already-unboxed",false)]
    public void IntegralLeavesRequireExactNativePeerLayoutAndWholeIr(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemInt32Type;
        Assert.That(owner.Fields.Any(f=>!f.IsStatic && f.Offset==0 && f.FieldType.FullName=="System.Int32"),Is.True);
        var method=new InjectedMethodAnalysisContext(owner,"Leaf",
            shape=="return-type"?app.SystemTypes.SystemUInt32Type:owner,
            MethodAttributes.Public|(shape=="static"?MethodAttributes.Static:0),
            shape=="arguments"?[owner]:[]);
        var self=new Register(null,"X0");method.ParameterOperands=[self];
        var memory=new MemoryOperand(self,addend:shape=="ir-offset"?20:16);
        if(shape=="ir-index")memory=new(self,new Register(null,"X1"),16,1);
        var move=new Instruction(0,OpCode.Move,self,memory){NativeReadSize=shape=="ir-width"?8:4};
        var instructions=new System.Collections.Generic.List<Instruction>{move,new(1,OpCode.Return,self)};
        if(shape=="extra-use")instructions.Insert(1,new(2,OpCode.Move,new Register(null,"X2"),self));
        method.ControlFlowGraph=new(instructions);
        var original=Convert.FromHexString("001040b9c0035fd6");
        var peer=Convert.FromHexString("000040b9c0035fd6");
        if(shape=="peer")peer[0]=1;
        if(shape=="incomplete")original=original[..4];
        if(shape=="native-store")original=Convert.FromHexString("001000b9c0035fd6");
        if(shape=="native-base")original[0]=0x20;
        if(shape=="native-destination")original[0]=1;
        if(shape=="field-offset")original=Convert.FromHexString("001440b9c0035fd6");
        if(shape=="already-unboxed")original=peer.ToArray();
        var before=method.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(InlineBoxedHfaRecovery.RecoverIntegralLeaf(method,original,peer)>0,Is.EqualTo(expected));
        if(expected)Assert.That(((MemoryOperand)move.Operands[1]).Addend,Is.Zero);
        else Assert.That(method.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
    }
}
