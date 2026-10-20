using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ExtendedArithmeticTests
{
    [TestCase(false, 0xdeadbeef00000003UL, 1048UL)]
    [TestCase(false, 0xffffffffffffffffUL, 68719477720UL)]
    [TestCase(true, 0xffffffffffffffffUL, 984UL)]
    [TestCase(true, 0xdeadbeef00000003UL, 1048UL)]
    public void LiftedExtensionExecutesWithCorrectHighBitsAndSignedness(bool signed, ulong payload, ulong expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Extended", t.SystemUInt64Type,
            MethodAttributes.Public | MethodAttributes.Static, [t.SystemUInt64Type, t.SystemUInt64Type], ["basis", "payload"]);
        var native = Disassembler.Disassemble(BitConverter.GetBytes(signed ? 0x8b29d108u : 0x8b295108u),
            0x17b5040, new(true, true, false)).Single();
        var lifted = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), [native, lifted, new List<ulong>(), context]);
        var basis = new LocalVariable("basis", new Register(null, "basis"), t.SystemUInt64Type);
        var value = new LocalVariable("payload", new Register(null, "payload"), t.SystemUInt64Type);
        var versions = new Dictionary<string, LocalVariable> { ["X8"] = basis, ["X9"] = value };
        var locals = new List<LocalVariable> { basis, value };
        foreach (var instruction in lifted)
        {
            var destination = (Register)instruction.Destination!;
            for (var i = 1; i < instruction.Operands.Count; i++)
                if (instruction.Operands[i] is Register register) instruction.SetOperand(i, versions[register.Name]);
            var type = instruction.OpCode == OpCode.NumericConvert ? (TypeAnalysisContext)instruction.Operands[1]
                : instruction.OpCode == OpCode.ShiftLeft ? ((LocalVariable)instruction.Operands[1]).Type! : t.SystemUInt64Type;
            var local = new LocalVariable("v" + locals.Count, destination, type);
            instruction.SetOperand(0, local); versions[destination.Name] = local; locals.Add(local);
        }
        lifted.Add(new(99, OpCode.Return, versions["X8"]));
        var assembly = new AssemblyDefinition("ExtendedFixture" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("ExtendedFixture.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Test", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Extended", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.UInt64, [module.CorLibTypeFactory.UInt64, module.CorLibTypeFactory.UInt64]));
        owner.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "basis", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "payload", 0));
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var slots = new Dictionary<LocalVariable, CilLocalVariable>();
        foreach (var local in locals)
        {
            TypeSignature signature = local.Type!.FullName switch { "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.UInt32" => module.CorLibTypeFactory.UInt32, "System.Int64" => module.CorLibTypeFactory.Int64,
                _ => module.CorLibTypeFactory.UInt64 };
            var slot = new CilLocalVariable(signature); slots.Add(local, slot); method.CilMethodBody.LocalVariables.Add(slot);
        }
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var instruction in lifted) emit.Invoke(null, [instruction, context, method, slots, method]);
        using var stream = new MemoryStream(); module.Write(stream);
        // Only this newly generated arithmetic fixture executes; no game code.
        var generated = Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Extended")!;
        Assert.That(generated.Invoke(null, [1000UL, payload]), Is.EqualTo(expected));
    }

    [TestCase(0x8b, false, 4)]
    [TestCase(0xcb, false, 4)]
    [TestCase(0xab, false, 4)]
    [TestCase(0xeb, false, 4)]
    [TestCase(0x8b, true, 4)]
    [TestCase(0xcb, true, 4)]
    [TestCase(0x8b, false, 0)]
    [TestCase(0x8b, true, 0)]
    public void ExtendThenShiftMustPrecedeArithmetic(byte high, bool signed, int shift)
    {
        // Original AWSConfigs.GetConfigEnum at RVA 17B5040: 08 51 29 8B.
        // Only the documented ADD/SUB/flags, extension and shift bits vary.
        uint encoding = (uint)(0x00294108 | (high << 24) | (shift << 10) | (signed ? 0x8000 : 0));
        var native = Disassembler.Disassemble(BitConverter.GetBytes(encoding), 0x17b5040, new(true, true, false)).Single();
        Assert.That(native.FinalOpExtendType, Is.EqualTo(signed ? Arm64ExtendType.SXTW : Arm64ExtendType.UXTW));
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Extended", t.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var emitted = new List<Instruction>(); var addresses = new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), [native, emitted, addresses, method]);
        Assert.That(emitted[0].OpCode, Is.EqualTo(OpCode.NumericConvert), "truncate the original W register, including stale high bits");
        Assert.That(((TypeAnalysisContext)emitted[0].Operands[1]).FullName, Is.EqualTo(signed ? "System.Int32" : "System.UInt32"));
        Assert.That(emitted[1].OpCode, Is.EqualTo(OpCode.NumericConvert));
        Assert.That(((TypeAnalysisContext)emitted[1].Operands[1]).FullName, Is.EqualTo(signed ? "System.Int64" : "System.UInt64"));
        Assert.That(emitted[1].Operands[3], Is.EqualTo(emitted[0].Destination));
        var arithmetic = emitted[shift == 0 ? 2 : 3];
        Assert.That(arithmetic.OpCode, Is.EqualTo(high is 0xcb or 0xeb ? OpCode.Subtract : OpCode.Add));
        Assert.That(arithmetic.NativeArithmeticSize, Is.EqualTo(8));
        if (shift != 0)
        {
            Assert.That(emitted[2].OpCode, Is.EqualTo(OpCode.ShiftLeft));
            Assert.That(emitted[2].Operands[1], Is.EqualTo(emitted[1].Destination));
            Assert.That(((Immediate)emitted[2].Operands[2]).Value, Is.EqualTo(shift));
            Assert.That(arithmetic.Operands[2], Is.EqualTo(emitted[2].Destination));
        }
        else Assert.That(arithmetic.Operands[2], Is.EqualTo(emitted[1].Destination));
        Assert.That(addresses.All(address => address == 0x17b5040), Is.True);
    }
}
