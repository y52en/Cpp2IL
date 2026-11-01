using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeFloatingPointWidthTests
{
    [TestCase(0x1e222820u,4)] // FADD S0,S1,S2
    [TestCase(0x1e622820u,8)] // FADD D0,D1,D2
    [TestCase(0x1e223820u,4)] // FSUB S0,S1,S2
    [TestCase(0x1e220820u,4)] // FMUL S0,S1,S2
    [TestCase(0x1e221820u,4)] // FDIV S0,S1,S2
    [TestCase(0x1e214020u,4)] // FNEG S0,S1
    [TestCase(0x1e204020u,4)] // FMOV S0,S1
    [TestCase(0x1e604020u,8)] // FMOV D0,D1
    [TestCase(0x1e2e1000u,4)] // FMOV S0,#1
    [TestCase(0x1e6e1000u,8)] // FMOV D0,#1
    [TestCase(0x1e260020u,0)] // FMOV W0,S1 is a bit transfer, not a numeric float copy
    [TestCase(0xaa0103e0u,0)] // MOV X0,X1
    public void NativeScalarPrecisionSurvivesLift(uint encoding,int expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Precision",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(BitConverter.GetBytes(encoding),0x1000,new(true,true,false)).Single();
        var emitted=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),new object[]{native,emitted,new List<ulong>(),method});
        Assert.That(emitted.Single().NativeFloatingPointSize,Is.EqualTo(expected));
    }

    [TestCase(4,0x3f800000UL)]
    [TestCase(4,0x80000000UL)]
    [TestCase(4,1UL)] // smallest subnormal is valid when native precision is proven
    [TestCase(8,0x3ff0000000000000UL)]
    [TestCase(8,0x8000000000000000UL)]
    [TestCase(8,1UL)]
    public void NativeArithmeticDecodesBitsIncludingNegativeZeroAndSubnormal(int width,ulong bits)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Bits",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var local=new LocalVariable("result",new Register(null,"result"));
        var operation=new Instruction(0,OpCode.Add,local,new Immediate(unchecked((long)bits)),new Immediate(0))
            {NativeFloatingPointSize=width};
        method.ControlFlowGraph=new ISILControlFlowGraph([operation,new Instruction(1,OpCode.Return)]);
        FloatLiteralRecovery.Run(method);
        var actual=width==4 ? (ulong)(uint)BitConverter.SingleToInt32Bits(((FloatLiteral)operation.Operands[1]).Value)
            : (ulong)BitConverter.DoubleToInt64Bits(((DoubleLiteral)operation.Operands[1]).Value);
        Assert.That(actual,Is.EqualTo(bits));
    }

    [Test]
    public void UntaggedIntegerArithmeticDoesNotBecomeFloat()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Integer",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var operation=new Instruction(0,OpCode.Add,new LocalVariable("n",new Register(null,"n")),new Immediate(1),new Immediate(2));
        method.ControlFlowGraph=new ISILControlFlowGraph([operation,new Instruction(1,OpCode.Return)]);
        FloatLiteralRecovery.Run(method);
        Assert.That(operation.Operands[1],Is.EqualTo(new Immediate(1)));
        Assert.That(operation.Operands[2],Is.EqualTo(new Immediate(2)));
    }

    [TestCase(OpCode.Add,0L)]
    [TestCase(OpCode.Subtract,0L)]
    [TestCase(OpCode.Multiply,1L)]
    [TestCase(OpCode.Negate,1065353216L)]
    public void NativeFloatingOperationsDoNotUseIntegerAlgebra(OpCode opcode,long bits)
    {
        var value=new Register(null,"V1");
        var operation=opcode==OpCode.Negate
            ? new Instruction(0,opcode,new Register(null,"V0"),new Immediate(bits))
            : new Instruction(0,opcode,new Register(null,"V0"),value,new Immediate(bits));
        operation.NativeFloatingPointSize=4;
        var graph=new ISILControlFlowGraph([operation,new Instruction(1,OpCode.Return)]);
        Assert.That(ConstantFolder.Run(graph),Is.False);
        Assert.That(operation.OpCode,Is.EqualTo(opcode));
        Assert.That(operation.Operands.Last(),Is.EqualTo(new Immediate(bits)));
    }
}
