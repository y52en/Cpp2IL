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
