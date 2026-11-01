using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64RightShiftedArithmeticTests
{
    static Arm64Instruction Native(bool wide, int operation, int kind, int amount, int right = 22)
    {
        // ADD, SUB, SUBS, CMP: real shifted-register encoding, not mocked fields.
        var word = 0x0b000000u | (wide ? 0x80000000u : 0) | (operation > 0 ? 0x40000000u : 0)
            | (operation > 1 ? 0x20000000u : 0) | ((uint)kind << 22) | ((uint)right << 16)
            | ((uint)amount << 10) | (19u << 5) | (operation == 3 ? 31u : 10u);
        return Disassembler.Disassemble(BitConverter.GetBytes(word), 0x1897b8c, new(true, true, false)).Single();
    }

    static IEnumerable<object[]> Cases()
    {
        foreach (var wide in new[] {false, true})
        foreach (var operation in Enumerable.Range(0, 4))
        foreach (var kind in new[] {1, 2})
        foreach (var amount in new[] {1, wide ? 63 : 31})
            yield return [wide, operation, kind, amount];
    }

    static ulong Expected(ulong bits, bool wide, int kind, int amount) => kind == 1
        ? wide ? bits >> amount : (uint)bits >> amount
        : wide ? unchecked((ulong)((long)bits >> amount)) : unchecked((uint)((int)bits >> amount));

    [TestCaseSource(nameof(Cases))]
    public void ActualDecodedArithmeticOperandPreservesWidthSignednessAndShiftBeforeUse(bool wide, int operation, int kind, int amount)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var native = Native(wide, operation, kind, amount);
        Assert.That(native.Mnemonic.ToString(), Is.EqualTo(new[] {"ADD", "SUB", "SUBS", "CMP"}[operation]));
        var contract = Arm64ShiftedArithmeticRecovery.LowerRight(native, app.SystemTypes);
        Assert.That(contract, Is.Not.Null, native.ToString());
        var code = contract!.Value.Operations.ToList();
        var type = wide ? app.SystemTypes.SystemUInt64Type : app.SystemTypes.SystemUInt32Type;
        code.Add(new(code.Count, OpCode.NumericConvert, new Register(null, "X10"), type, type, contract.Value.Operand));
        foreach (var bits in new[] {0UL, 1UL, 0x7fffffffUL, 0x80000000UL, 0xffffffffUL, 0x8000000000000000UL, ulong.MaxValue})
            Assert.That(Arm64ShiftedLogicalTests.Execute(code, 0, bits), Is.EqualTo(Expected(bits, wide, kind, amount)));
        Assert.That(contract.Value.Operations[0].NativeIntegerSourceView, Is.True);

        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Arithmetic",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var actual = new List<Instruction>(); var addresses = new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), [native, actual, addresses, method]);
        Assert.That(actual.Take(3).Select(i => i.OpCode), Is.EqualTo(contract.Value.Operations.Select(i => i.OpCode)));
        Assert.That(addresses, Is.All.EqualTo(0x1897b8cUL));
        if (operation < 3)
        {
            Assert.That(actual[3].OpCode, Is.EqualTo(operation == 0 ? OpCode.Add : OpCode.Subtract));
            Assert.That(actual[3].Operands[2], Is.TypeOf<Register>());
            Assert.That(((Register)actual[3].Operands[2]).Name, Is.EqualTo(contract.Value.Operand.Name));
            Assert.That(actual[3].NativeArithmeticSize, Is.EqualTo(wide ? 8 : 4));
        }
        if (operation > 1)
            Assert.That(actual.Any(i => i.UnsignedComparison && i.NativeComparisonSize == (wide ? 8 : 4)), Is.True);
    }

    [TestCase(false, 1)] [TestCase(false, 2)] [TestCase(true, 1)] [TestCase(true, 2)]
    public void ActualGeneratedCilPreservesHighBitsAndWordZeroExtension(bool wide, int kind)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var amount = wide ? 63 : 31;
        var contract = Arm64ShiftedArithmeticRecovery.LowerRight(Native(wide, 0, kind, amount), app.SystemTypes)!.Value;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Calculate",
            app.SystemTypes.SystemUInt64Type, MethodAttributes.Public | MethodAttributes.Static, [app.SystemTypes.SystemUInt64Type]);
        var input = new LocalVariable("input", new Register(null, "X22"), app.SystemTypes.SystemUInt64Type);
        var locals = new Dictionary<string, LocalVariable> {{"X22", input}};
        var instructions = new List<Instruction>();
        foreach (var instruction in contract.Operations)
        {
            var destination = (Register)instruction.Operands[0];
            var type = instruction.OpCode == OpCode.NumericConvert ? (TypeAnalysisContext)instruction.Operands[1]
                : locals[((Register)instruction.Operands[1]).Name].Type!;
            locals[destination.Name] = new(destination.Name, destination, type);
            var operands = instruction.Operands.Select(o => o is Register r ? (IOperand)locals[r.Name] : o).ToList();
            instructions.Add(new(instructions.Count, instruction.OpCode, operands)
                {NativeArithmeticSize = instruction.NativeArithmeticSize, NativeIntegerSourceView = instruction.NativeIntegerSourceView});
        }
        instructions.Add(new(instructions.Count, OpCode.Return, locals[contract.Operand.Name]));
        context.ControlFlowGraph = new(instructions); context.ParameterLocals.Add(input);
        var assembly = new AssemblyDefinition("ArithmeticShift" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("ArithmeticShift.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Fixture", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(owner);
        var generated = new MethodDefinition("Calculate", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.UInt64, [module.CorLibTypeFactory.UInt64]));
        generated.CilMethodBody = new CilMethodBody {InitializeLocals = true}; owner.Methods.Add(generated);
        TypeSignature Signature(TypeAnalysisContext type) => type.FullName switch
        {
            "System.Int32" => module.CorLibTypeFactory.Int32, "System.UInt32" => module.CorLibTypeFactory.UInt32,
            "System.Int64" => module.CorLibTypeFactory.Int64, "System.UInt64" => module.CorLibTypeFactory.UInt64,
            _ => throw new InvalidOperationException(type.FullName),
        };
        var ilLocals = locals.Values.ToDictionary(v => v, v => new CilLocalVariable(Signature(v.Type!)));
        foreach (var local in ilLocals.Values) generated.CilMethodBody.LocalVariables.Add(local);
        generated.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        generated.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, ilLocals[input]);
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var instruction in instructions) emit.Invoke(null, [instruction, context, generated, ilLocals, generated]);
        using var stream = new MemoryStream(); module.Write(stream);
        var executable = Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Calculate")!;
        foreach (var bits in new[] {0UL, 1UL, 0x7fffffffUL, 0x80000000UL, uint.MaxValue, 0x8000000000000000UL, ulong.MaxValue})
            Assert.That(executable.Invoke(null, [bits]), Is.EqualTo(Expected(bits, wide, kind, amount)));
    }

    [Test]
    public void UnshiftedLeftShiftAndSeparatelyProvedAdditionFlagsRemainOnExistingPaths()
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        Assert.That(Arm64ShiftedArithmeticRecovery.LowerRight(Native(false, 0, 1, 0), types), Is.Null);
        Assert.That(Arm64ShiftedArithmeticRecovery.LowerRight(Native(false, 0, 0, 1), types), Is.Null);
        var adds = Disassembler.Disassemble(BitConverter.GetBytes(0x2b567e6au), 0, new(true, true, false)).Single();
        Assert.That(Arm64ShiftedArithmeticRecovery.LowerRight(adds, types), Is.Null);
    }

    [TestCase(false)] [TestCase(true)]
    public void ZeroRegisterIsReadAsZeroBeforeTheShift(bool wide)
    {
        var contract = Arm64ShiftedArithmeticRecovery.LowerRight(Native(wide, 0, 1, 1, 31), TestGameLoader.LoadSimple2019Game().SystemTypes)!.Value;
        Assert.That(contract.Operations[0].Operands[3], Is.TypeOf<Immediate>());
        Assert.That(((Immediate)contract.Operations[0].Operands[3]).Value, Is.Zero);
    }
}
