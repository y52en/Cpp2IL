using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64FloatImmediateTests
{
    [TestCase(0x1e2e1000u, false, 1d)] // FMOV S0, #1.0
    [TestCase(0x1e2e101fu, false, 1d)] // FMOV S31, #1.0
    [TestCase(0x1e3e1000u, false, -1d)]
    [TestCase(0x1e6e1000u, true, 1d)]  // FMOV D0, #1.0
    [TestCase(0x1e6e101fu, true, 1d)]  // FMOV D31, #1.0
    [TestCase(0x1e7e1000u, true, -1d)]
    public void RealFmovImmediateRetainsNativePrecision(uint encoding, bool wide, double expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "FloatImmediate",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var native = Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0x1000, new(true, true, false)).Single();
        Assert.That(native.Mnemonic, Is.EqualTo(Arm64Mnemonic.FMOV));
        Assert.That(native.Op1Kind, Is.EqualTo(Arm64OperandKind.FloatingPointImmediate));
        var emitted = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { native, emitted, new List<ulong>(), method });
        var move = emitted.Single(i => i.OpCode == OpCode.Move);
        if (wide)
        {
            Assert.That(move.Operands[1], Is.TypeOf<DoubleLiteral>());
            Assert.That(((DoubleLiteral)move.Operands[1]).Value, Is.EqualTo(expected));
        }
        else
        {
            Assert.That(move.Operands[1], Is.TypeOf<FloatLiteral>());
            Assert.That(((FloatLiteral)move.Operands[1]).Value, Is.EqualTo((float)expected));
        }
    }
}
