using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64WritebackWidthTests
{
    [TestCase(0xb8010f60u, true, false)] // STR W0,[X27,#16]!
    [TestCase(0xb8010760u, false, false)] // STR W0,[X27],#16
    [TestCase(0xb8410f60u, true, true)] // LDR W0,[X27,#16]!
    [TestCase(0xb8410760u, false, true)] // LDR W0,[X27],#16
    public void DataAccessWidthAndPointerWritebackWidthAreIndependent(uint bits, bool pre, bool read)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var native = Disassembler.Disassemble(BitConverter.GetBytes(bits), 0x1000, new(true, true, false)).Single();
        Assert.That(native.MemBase.ToString(), Is.EqualTo("X27"));
        Assert.That(native.MemOffset, Is.EqualTo(16));
        Assert.That(native.MemIndexMode.ToString(), Is.EqualTo(pre ? "PreIndex" : "PostIndex"));
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { native, instructions, new List<ulong>(), caller });
        var update = instructions.Single(i => i.OpCode == OpCode.Add);
        var access = instructions.Single(i => i.OpCode == OpCode.Move);
        Assert.That(update.NativeArithmeticSize, Is.EqualTo(8));
        Assert.That(read ? access.NativeReadSize : access.NativeWriteSize, Is.EqualTo(4));
        Assert.That(instructions.IndexOf(update) < instructions.IndexOf(access), Is.EqualTo(pre));
    }
}
