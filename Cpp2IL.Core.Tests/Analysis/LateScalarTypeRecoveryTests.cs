using System.Reflection;
using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateScalarTypeRecoveryTests
{
    static LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new Register(null, name), type);
    static MethodAnalysisContext Method(ApplicationAnalysisContext app, params Instruction[] instructions)
    {
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new(instructions.ToList());
        return method;
    }
    static Instruction Arithmetic(LocalVariable result, IOperand left, IOperand right, int width, OpCode op = OpCode.Multiply)
        => new(1, op, result, left, right) {NativeArithmeticSize = width};

    [TestCase(4, OpCode.Add)]
    [TestCase(4, OpCode.Subtract)]
    [TestCase(4, OpCode.Multiply)]
    [TestCase(8, OpCode.Add)]
    [TestCase(8, OpCode.Subtract)]
    [TestCase(8, OpCode.Multiply)]
    public void ExactScalarFactsFollowOriginalNativeWidthWithoutChangingGraph(int width, OpCode op)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var source = Local("input", app.SystemTypes.SystemInt32Type);
        var result = Local("result");
        var operation = Arithmetic(result, source, new Immediate(-1), width, op);
        var returned = new Instruction(2, OpCode.Return, result);
        var method = Method(app, operation, returned); method.ParameterLocals.Add(source);
        var graph = method.ControlFlowGraph!;
        var originals = graph.Instructions.ToArray();
        var operands = operation.Operands.ToArray();
        Assert.That(LateScalarTypeRecovery.Run(method), Is.EqualTo(1));
        Assert.That(result.Type?.FullName, Is.EqualTo(width == 4 ? "System.UInt32" : "System.Int64"));
        Assert.That(source.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(graph.Instructions, Is.EqualTo(originals));
        Assert.That(operation.Operands.ToArray(), Is.EqualTo(operands));
        Assert.That(operation.NativeArithmeticSize, Is.EqualTo(width));
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
    }

    [Test]
    public void LogicalCopiesAndDependentArithmeticReachAMonotonicFixpoint()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var source = Local("input", app.SystemTypes.SystemInt64Type);
        var first = Local("first"); var copy = Local("copy"); var last = Local("last");
        var method = Method(app, Arithmetic(first, source, new Immediate(4), 8),
            new(-1, OpCode.Move, copy, first), Arithmetic(last, copy, new Immediate(1), 8, OpCode.Add),
            new(3, OpCode.Return, last));
        method.ParameterLocals.Add(source);
        Assert.That(LateScalarTypeRecovery.Run(method), Is.EqualTo(3));
        Assert.That(new[]{first, copy, last}.Select(v => v.Type?.FullName), Is.All.EqualTo("System.Int64"));
    }

    [TestCase("reference")]
    [TestCase("float")]
    [TestCase("boolean")]
    [TestCase("unknown")]
    [TestCase("pointer")]
    [TestCase("two-constants")]
    public void RegisterWidthAloneNeverInventsIntegerProvenance(string kind)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var source = Local("input", kind switch {"reference" => types.SystemObjectType,
            "float" => types.SystemSingleType, "boolean" => types.SystemBooleanType,
            "pointer" => new PointerTypeAnalysisContext(types.SystemInt32Type), _ => null});
        var result = Local("result");
        var method = Method(app, Arithmetic(result, kind == "two-constants" ? new Immediate(5) : source,
            new Immediate(4), 8), new(2, OpCode.Return, result));
        method.ParameterLocals.Add(source);
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
        Assert.That(result.Type, Is.Null);
    }

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(16)]
    public void MissingOrNonScalarNativeWidthIsNotAccepted(int width)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var source = Local("input", app.SystemTypes.SystemInt32Type);
        var result = Local("result");
        var method = Method(app, Arithmetic(result, source, new Immediate(2), width), new(2, OpCode.Return, result));
        method.ParameterLocals.Add(source);
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
    }

    [TestCase("address")]
    [TestCase("dereference")]
    [TestCase("multiple-definitions")]
    [TestCase("implicit-clobber")]
    [TestCase("input-clobber")]
    [TestCase("self-use")]
    [TestCase("already-typed")]
    public void EscapingClobberedOrAmbiguousStorageIsNotRetagged(string kind)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var source = Local("input", app.SystemTypes.SystemInt32Type);
        var result = Local("result", kind == "already-typed" ? app.SystemTypes.SystemUInt64Type : null);
        var operation = Arithmetic(result, kind == "self-use" ? result : source, new Immediate(3), 8);
        var instructions = new List<Instruction>{operation};
        if (kind == "multiple-definitions") instructions.Add(new(2, OpCode.Move, result, new Immediate(5)));
        if (kind is "implicit-clobber" or "input-clobber") instructions.Add(new(2, OpCode.Nop)
            {ImplicitDefinition = kind == "input-clobber" ? source.Register : result.Register});
        IOperand use = kind == "address" ? new AddressOf(result) : kind == "dereference"
            ? new MemoryOperand(result, null, 0, 0) : result;
        instructions.Add(new(3, OpCode.Return, use));
        var method = Method(app, instructions.ToArray()); method.ParameterLocals.Add(source);
        var previous = result.Type;
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
        Assert.That(result.Type, Is.SameAs(previous));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AValueDefinedOnOnlyOneIncomingEdgeIsNotGloballyTyped(bool missingSourceDefinition)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var parameter = Local("parameter", app.SystemTypes.SystemInt32Type);
        var source = Local("source", app.SystemTypes.SystemInt32Type); var result = Local("result");
        var method = Method(app, new Instruction(0, OpCode.Return)); method.ParameterLocals.Add(parameter);
        var entry = new Block{ID = 0}; var left = new Block{ID = 1}; var right = new Block{ID = 2};
        var join = new Block{ID = 3}; var exit = new Block{ID = 4};
        entry.Successors = [left, right]; left.Predecessors = [entry]; right.Predecessors = [entry];
        left.Successors = [join]; right.Successors = [join]; join.Predecessors = [left, right];
        join.Successors = [exit]; exit.Predecessors = [join];
        if (missingSourceDefinition)
        {
            left.Instructions = [new(1, OpCode.Move, source, parameter) {NativeRegisterCopySize = 4}];
            join.Instructions = [Arithmetic(result, source, new Immediate(1), 4), new(3, OpCode.Return, result)];
        }
        else
        {
            left.Instructions = [Arithmetic(result, parameter, new Immediate(1), 4)];
            join.Instructions = [new(3, OpCode.Return, result)];
        }
        var graph = method.ControlFlowGraph!;
        graph.EntryBlock = entry; graph.ExitBlock = exit; graph.Blocks = [entry, left, right, join, exit];
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
        Assert.That(result.Type, Is.Null);
    }

    [TestCase(4, 8)]
    [TestCase(8, 4)]
    public void PhysicalCopiesDoNotInventNarrowingOrExtension(int sourceWidth, int copyWidth)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var source = Local("input", sourceWidth == 4 ? app.SystemTypes.SystemInt32Type : app.SystemTypes.SystemInt64Type);
        var copy = Local("copy");
        var method = Method(app, new Instruction(1, OpCode.Move, copy, source) {NativeRegisterCopySize = copyWidth},
            new(2, OpCode.Return, copy)); method.ParameterLocals.Add(source);
        Assert.That(LateScalarTypeRecovery.Run(method), Is.Zero);
    }

    [TestCase("Int32", 4, 0, true)]
    [TestCase("Int32", 8, 0, false)]
    [TestCase("Int32", 0, 0, false)]
    [TestCase("Object", 8, 0, false)]
    [TestCase("Boolean", 1, 0, false)]
    [TestCase("UInt64", 8, 0, true)]
    [TestCase("UInt64", 8, 1, false)]
    public void LateFieldFactsRequireExactScalarReadExtent(string name, int readWidth, int writeWidth, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System." + name)!;
        var field = new InjectedFieldAnalysisContext("Value", type, FieldAttributes.Public, app.SystemTypes.SystemObjectType, 16);
        var receiver = Local("receiver", app.SystemTypes.SystemObjectType); var result = Local("result");
        var load = new Instruction(0, OpCode.Move, result, new FieldReference(field, receiver, 16))
            {NativeReadSize = readWidth, NativeWriteSize = writeWidth};
        var method = Method(app, load, new(1, OpCode.Return, result));
        Assert.That(LateScalarTypeRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        Assert.That(result.Type, Is.SameAs(expected ? type : null));
    }

    [TestCase("Int32", 4, OpCode.Add)]
    [TestCase("Int32", 4, OpCode.Subtract)]
    [TestCase("Int32", 4, OpCode.Multiply)]
    [TestCase("Int32", 8, OpCode.Add)]
    [TestCase("Int32", 8, OpCode.Subtract)]
    [TestCase("Int32", 8, OpCode.Multiply)]
    [TestCase("UInt32", 4, OpCode.Add)]
    [TestCase("UInt32", 4, OpCode.Subtract)]
    [TestCase("UInt32", 4, OpCode.Multiply)]
    [TestCase("UInt32", 8, OpCode.Add)]
    [TestCase("UInt32", 8, OpCode.Subtract)]
    [TestCase("UInt32", 8, OpCode.Multiply)]
    [TestCase("Int64", 4, OpCode.Add)]
    [TestCase("Int64", 4, OpCode.Subtract)]
    [TestCase("Int64", 4, OpCode.Multiply)]
    [TestCase("Int64", 8, OpCode.Add)]
    [TestCase("Int64", 8, OpCode.Subtract)]
    [TestCase("Int64", 8, OpCode.Multiply)]
    [TestCase("UInt64", 4, OpCode.Add)]
    [TestCase("UInt64", 4, OpCode.Subtract)]
    [TestCase("UInt64", 4, OpCode.Multiply)]
    [TestCase("UInt64", 8, OpCode.Add)]
    [TestCase("UInt64", 8, OpCode.Subtract)]
    [TestCase("UInt64", 8, OpCode.Multiply)]
    public void ActualCilExecutionKeepsNativeWordBitsThroughWideReturn(string source, int width, OpCode operation)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var sourceType = app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System." + source)!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Calculate", app.SystemTypes.SystemUInt64Type,
            MethodAttributes.Public | MethodAttributes.Static, [sourceType]);
        var input = Local("input", sourceType); var result = Local("result");
        var instruction = Arithmetic(result, input, new Immediate(3), width, operation);
        var returned = new Instruction(2, OpCode.Return, result);
        context.ControlFlowGraph = new([instruction, returned]); context.ParameterLocals.Add(input);
        Assert.That(LateScalarTypeRecovery.Run(context), Is.EqualTo(1));
        var assembly = new AssemblyDefinition("LateScalar" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("LateScalar.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Fixture", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(owner);
        TypeSignature Signature(string name) => name switch {"Int32" => module.CorLibTypeFactory.Int32,
            "UInt32" => module.CorLibTypeFactory.UInt32, "Int64" => module.CorLibTypeFactory.Int64,
            "UInt64" => module.CorLibTypeFactory.UInt64, _ => throw new ArgumentException(name)};
        var generatedMethod = new MethodDefinition("Calculate", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.UInt64, [Signature(source)]));
        owner.Methods.Add(generatedMethod); generatedMethod.CilMethodBody = new CilMethodBody {InitializeLocals = true};
        var ilInput = new CilLocalVariable(Signature(source));
        var ilResult = new CilLocalVariable(Signature(result.Type!.FullName.Substring("System.".Length)));
        generatedMethod.CilMethodBody.LocalVariables.Add(ilInput); generatedMethod.CilMethodBody.LocalVariables.Add(ilResult);
        generatedMethod.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        generatedMethod.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, ilInput);
        var locals = new Dictionary<LocalVariable, CilLocalVariable> {{input, ilInput}, {result, ilResult}};
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        emit.Invoke(null, [instruction, context, generatedMethod, locals, generatedMethod]);
        emit.Invoke(null, [returned, context, generatedMethod, locals, generatedMethod]);
        using var stream = new MemoryStream(); module.Write(stream);
        var executable = Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Calculate")!;
        foreach (var bits in new[] {0UL, 0x7fffffffUL, 0x80000000UL, uint.MaxValue, ulong.MaxValue})
        {
            object value = source switch {"Int32" => unchecked((int)bits), "UInt32" => (uint)bits,
                "Int64" => unchecked((long)bits), _ => bits};
            var inputBits = source == "Int32" ? unchecked((ulong)(long)(int)bits) : source == "UInt32" ? (uint)bits : bits;
            var expected = operation switch {OpCode.Add => unchecked(inputBits + 3),
                OpCode.Subtract => unchecked(inputBits - 3), _ => unchecked(inputBits * 3)};
            if (width == 4) expected = (uint)expected;
            Assert.That(executable.Invoke(null, [value]), Is.EqualTo(expected));
        }
    }
}
