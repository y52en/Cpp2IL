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
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CoalescedParameterIdentityTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void GeneratedFixtureReturnsTheActualIncomingValue(bool reference)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = reference ? t.SystemStringType : t.SystemInt32Type;
        var input = new LocalVariable("input", new Register(0, "X0"), type);
        var copy = new LocalVariable("copy", new Register(0, "X0", 1), type);
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Identity", type,
            MethodAttributes.Public | MethodAttributes.Static, [type], ["input"])
        {
            ControlFlowGraph = new([new(0, OpCode.Move, copy, input), new(1, OpCode.Return, copy)]),
            ParameterLocals = [input], Locals = [input, copy]
        };
        CopyCoalescer.Run(context);
        var assembly = new AssemblyDefinition("ArgumentIdentity" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("ArgumentIdentity.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Test", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var signature = reference ? module.CorLibTypeFactory.String : module.CorLibTypeFactory.Int32;
        var method = new MethodDefinition("Identity", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static, MethodSignature.CreateStatic(signature, [signature]));
        owner.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "input", 0));
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var locals = new Dictionary<LocalVariable, CilLocalVariable>();
        foreach (var local in context.Locals)
        {
            var slot = new CilLocalVariable(signature);
            locals.Add(local, slot);
            method.CilMethodBody.LocalVariables.Add(slot);
        }
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var instruction in context.ControlFlowGraph.Instructions)
            emit.Invoke(null, [instruction, context, method, locals, method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Ldarg), Is.True);
        using var stream = new MemoryStream();
        module.Write(stream);
        var identity = Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Identity")!;
        // Execute only our two-instruction fixture, never any recovered game code.
        object value = reference ? "argument must survive" : 413;
        Assert.That(identity.Invoke(null, [value]), Is.EqualTo(value));
    }

    [TestCase("reference")]
    [TestCase("integer")]
    [TestCase("this")]
    [TestCase("addressed-input")]
    public void OrdinaryArgumentCannotBecomeAnUninitializedLocal(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var type = shape == "integer" ? t.SystemInt32Type : t.SystemStringType;
        var input = new LocalVariable("input", new Register(0, "X0"), type) { IsThis = shape == "this" };
        var first = new LocalVariable("v1", new Register(0, "X0", 1), type);
        var second = new LocalVariable("v2", new Register(0, "X0", 2), type);
        var instructions = new List<Instruction> { new(0, OpCode.Move, first, input), new(1, OpCode.Move, second, first), new(2, OpCode.Return, second) };
        if (shape == "addressed-input") instructions.Insert(0, new(3, OpCode.CallVoid, new StringLiteral("observe"), new AddressOf(input)));
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", type, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = new(instructions), ParameterLocals = [input], Locals = [input, first, second] };
        CopyCoalescer.Run(method);
        var result = (LocalVariable)method.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Return).Operands[0];
        var seen = new HashSet<LocalVariable>();
        while (!ReferenceEquals(result, input) && seen.Add(result))
        {
            var writes = method.ControlFlowGraph.Instructions.Where(i => ReferenceEquals(i.Destination, result)).ToArray();
            Assert.That(writes, Has.Length.EqualTo(1), "input value was erased; IL emission would read an uninitialized local");
            Assert.That(writes[0].OpCode, Is.EqualTo(OpCode.Move));
            result = (LocalVariable)writes[0].Operands[1];
        }
        Assert.That(result, Is.SameAs(input));
        Assert.That(input.Name, Is.EqualTo("input"));
    }

    [Test]
    public void OrdinaryLocalCopiesStillCoalesce()
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var first = new LocalVariable("a", new Register(0, "X0", 1), t.SystemInt32Type);
        var second = new LocalVariable("b", new Register(0, "X0", 2), t.SystemInt32Type);
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemInt32Type, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = new([new(0, OpCode.Move, first, new Immediate(1)), new(1, OpCode.Move, second, first), new(2, OpCode.Return, second)]),
              ParameterLocals = [], Locals = [first, second] };
        CopyCoalescer.Run(method);
        Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Move && i.Operands[1] is LocalVariable), Is.False);
    }
}
