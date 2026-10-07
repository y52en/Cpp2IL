using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class BooleanAndNullRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext Context(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var context = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        context.Locals = locals.ToList();
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        return context;
    }

    [TestCase(OpCode.Not)]
    [TestCase(OpCode.And)]
    [TestCase(OpCode.Or)]
    [TestCase(OpCode.Xor)]
    public void BooleanOperations_PropagateResultType(OpCode op)
    {
        var boolean = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemBooleanType;
        var left = new LocalVariable("left", new Register(null, "left"), boolean);
        var right = new LocalVariable("right", new Register(null, "right"), boolean);
        var result = new LocalVariable("result", new Register(null, "result"));
        var instruction = op == OpCode.Not ? new Instruction(0, op, result, left) : new Instruction(0, op, result, left, right);
        var context = Context([instruction, new(1, OpCode.Return)], left, right, result);
        LocalVariables.ResolveTypesAndFields(context);
        Assert.That(result.Type, Is.SameAs(boolean));
    }

    [TestCase(OpCode.And, 0, false)]
    [TestCase(OpCode.And, 1, true)]
    [TestCase(OpCode.Or, 0, true)]
    [TestCase(OpCode.Or, 1, false)]
    [TestCase(OpCode.Xor, 0, false)]
    [TestCase(OpCode.Xor, 1, true)]
    public void BooleanOperations_AcceptOnlyCanonicalConstants(OpCode op, int value, bool constantFirst)
    {
        var boolean = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemBooleanType;
        var flag = new LocalVariable("flag", new Register(null, "flag"), boolean);
        var result = new LocalVariable("result", new Register(null, "result"));
        IOperand left = constantFirst ? Imm(value) : flag;
        IOperand right = constantFirst ? flag : Imm(value);
        var context = Context([new(0, op, result, left, right), new(1, OpCode.Return)], flag, result);
        LocalVariables.ResolveTypesAndFields(context);
        Assert.That(result.Type, Is.SameAs(boolean));
    }

    [TestCase(OpCode.And)]
    [TestCase(OpCode.Or)]
    [TestCase(OpCode.Xor)]
    public void BooleanOperations_DoNotMistypeNonCanonicalMask(OpCode op)
    {
        var boolean = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemBooleanType;
        var flag = new LocalVariable("flag", new Register(null, "flag"), boolean);
        var result = new LocalVariable("result", new Register(null, "result"));
        var context = Context([new(0, op, result, flag, Imm(2)), new(1, OpCode.Return)], flag, result);
        LocalVariables.ResolveTypesAndFields(context);
        Assert.That(result.Type, Is.Null);
    }

    [Test]
    public void IntegerComplement_RemainsInteger()
    {
        var integer = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var input = new LocalVariable("input", new Register(null, "input"), integer);
        var result = new LocalVariable("result", new Register(null, "result"));
        var context = Context([new(0, OpCode.Not, result, input), new(1, OpCode.Return)], input, result);
        LocalVariables.ResolveTypesAndFields(context);
        Assert.That(result.Type, Is.SameAs(integer));
    }

    [TestCase(0, true, 1)]
    [TestCase(1, true, 0)]
    [TestCase(2, true, 0)]
    [TestCase(-1, true, 0)]
    [TestCase(0, false, -1)]
    [TestCase(1, false, -2)]
    public void ConstantNot_SeparatesLogicalNegationFromBitwiseComplement(int input, bool boolean, int expected)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var result = new LocalVariable("result", new Register(null, "result"), boolean ? types.SystemBooleanType : types.SystemInt32Type);
        var instruction = new Instruction(0, OpCode.Not, result, Imm(input));
        var context = Context([instruction, new(1, OpCode.Return)], result);
        Assert.That(ConstantFolder.Run(context), Is.True);
        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(instruction.Operands[1], Is.EqualTo(Imm(expected)));
    }

    [TestCase(0x80000000L, false)]
    [TestCase(0xffffffffL, false)]
    [TestCase(0x100000000L, false)]
    [TestCase(0x80000000L, true)]
    public void BitwiseMask_RespectsDeclaredIntegerWidth(long mask, bool wide)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var integer = wide ? types.SystemInt64Type : types.SystemInt32Type;
        var input = new LocalVariable("input", new Register(null, "input"), integer);
        var result = new LocalVariable("result", new Register(null, "result"), integer);
        var context = Context([new(0, OpCode.And, result, input, Imm(mask)), new(1, OpCode.Return)], input, result);
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var corlib = new ModuleDefinition("mscorlib.dll");
        var definition = new TypeDefinition("System", integer.Name, TypeAttributes.Public);
        corlib.TopLevelTypes.Add(definition);
        integer.PutExtraData("AsmResolverType", definition);
        var type = new TypeDefinition("Cpp2IL.Core.Tests", "BitwiseMask", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldc_I8), Is.EqualTo(wide || mask > uint.MaxValue));
        if (!wide && mask <= uint.MaxValue)
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldc_I4 && i.Operand is int value && value == unchecked((int)mask)), Is.True);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ManagedByrefStore_WritesReferentAndPreservesPointer(bool reference)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var element = reference ? types.SystemObjectType : types.SystemInt32Type;
        var pointer = new LocalVariable("output", new Register(null, "output"), new ByRefTypeAnalysisContext(element));
        var context = Context([new(0, OpCode.Move, new MemoryOperand(pointer), Imm(0)), new(1, OpCode.Return)], pointer);
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var corlib = new ModuleDefinition("mscorlib.dll");
        var elementDefinition = new TypeDefinition("System", element.Name, TypeAttributes.Public);
        corlib.TopLevelTypes.Add(elementDefinition);
        element.PutExtraData("AsmResolverType", elementDefinition);
        var type = new TypeDefinition("Cpp2IL.Core.Tests", "ByrefStore", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [(reference ? module.CorLibTypeFactory.Object : module.CorLibTypeFactory.Int32).MakeByReferenceType()]));
        type.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "output", ParameterAttributes.Out));
        IlGenerator.GenerateIl(context, method);
        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == (reference ? CilOpCodes.Stind_Ref : CilOpCodes.Stobj)), Is.True);
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldarg), Is.True);
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.EqualTo(reference));
        Assert.That(body.Instructions.Where(i => i.OpCode == CilOpCodes.Stloc).All(i => i.Operand != body.LocalVariables[0]), Is.True,
            "the byref local must not be replaced by the stored value");
    }

    [TestCase(OpCode.CheckEqual, false, true)]
    [TestCase(OpCode.CheckEqual, true, true)]
    [TestCase(OpCode.CheckNotEqual, false, true)]
    [TestCase(OpCode.CheckNotEqual, true, true)]
    [TestCase(OpCode.CheckEqual, false, false)]
    [TestCase(OpCode.CheckEqual, true, false)]
    public void ZeroComparison_UsesNullOnlyForReferenceTypes(OpCode op, bool zeroFirst, bool reference)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var input = new LocalVariable("input", new Register(null, "input"), reference ? types.SystemObjectType : types.SystemInt32Type);
        var result = new LocalVariable("result", new Register(null, "result"), types.SystemBooleanType);
        IOperand left = zeroFirst ? Imm(0) : input;
        IOperand right = zeroFirst ? input : Imm(0);
        var context = Context([new(0, op, result, left, right), new(1, OpCode.Return)], input, result);
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var corlib = new ModuleDefinition("mscorlib.dll");
        foreach (var systemType in new[] { types.SystemObjectType, types.SystemInt32Type, types.SystemBooleanType })
        {
            var definition = new TypeDefinition("System", systemType.Name, TypeAttributes.Public);
            corlib.TopLevelTypes.Add(definition);
            systemType.PutExtraData("AsmResolverType", definition);
        }
        var type = new TypeDefinition("Cpp2IL.Core.Tests", "NullComparison", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.EqualTo(reference));
    }
}
