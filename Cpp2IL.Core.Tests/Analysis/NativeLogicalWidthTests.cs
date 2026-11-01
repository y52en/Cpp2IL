using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeLogicalWidthTests
{
    [TestCase(0x9240f514u, OpCode.And, 8)] // Original DateTimeParse: AND X20,X8,#low62.
    [TestCase(0x12001d14u, OpCode.And, 4)] // AND W20,W8,#0xff.
    [TestCase(0x8a020020u, OpCode.And, 8)] // AND X0,X1,X2.
    [TestCase(0x0a020020u, OpCode.And, 4)] // AND W0,W1,W2.
    [TestCase(0xaa020020u, OpCode.Or, 8)]
    [TestCase(0x2a020020u, OpCode.Or, 4)]
    [TestCase(0xca020020u, OpCode.Xor, 8)]
    [TestCase(0x4a020020u, OpCode.Xor, 4)]
    [TestCase(0x52001d14u, OpCode.Xor, 4)] // EOR W20,W8,#0xff.
    [TestCase(0xb2401d14u, OpCode.Or, 8)] // ORR X20,X8,#0xff.
    [TestCase(0xaa0103e0u, OpCode.Move, 0)] // MOV alias keeps its own copy contract.
    [TestCase(0x1e222820u, OpCode.Add, 0)] // FADD must not acquire an integer width.
    public void ActualDecodedInstructionRetainsWidthBeforeWAndXNormalization(uint encoding, OpCode opcode, int width)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Width",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var native = Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0x12bd378, new(true, true, false)).Single();
        var emitted = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { native, emitted, new List<ulong>(), method });
        var operation = emitted.Single();
        Assert.That(operation.OpCode, Is.EqualTo(opcode));
        Assert.That(operation.NativeArithmeticSize, Is.EqualTo(width));
        if (encoding == 0x9240f514u)
        {
            Assert.That(((Immediate)operation.Operands[2]).Value, Is.EqualTo(0x3fffffffffffffffL));
            Assert.That(((Register)operation.Operands[0]).Name, Is.EqualTo("X20"));
        }
    }
}
