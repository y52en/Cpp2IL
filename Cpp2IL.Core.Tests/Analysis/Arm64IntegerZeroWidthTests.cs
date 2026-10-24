using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64IntegerZeroWidthTests
{
    [TestCase(0xd2800004u, 8)] // MOV X4,#0
    [TestCase(0x52800004u, 8)] // MOV W4,#0; upper X4 is also zero
    [TestCase(0xaa1f03e4u, 8)] // MOV X4,XZR
    [TestCase(0x2a1f03e4u, 8)] // MOV W4,WZR
    [TestCase(0x52800024u, 0)] // MOV W4,#1
    [TestCase(0xaa0103e4u, 0)] // MOV X4,X1
    public void WholeRegisterZeroRequiresActualNativeZeroCopy(uint encoding, int expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Zero",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var native = Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0x1000, new(true, true, false)).Single();
        var emitted = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), [native, emitted, new List<ulong>(), method]);
        Assert.That(emitted.Single(i => i.OpCode == OpCode.Move).NativeZeroSize, Is.EqualTo(expected));
    }
}
