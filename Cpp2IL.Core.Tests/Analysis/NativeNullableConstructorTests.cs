using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeNullableConstructorTests
{
    [TestCase(false, false)]
    [TestCase(true, true)]
    public void NativeReadOnlyGetterCanFollowAnEntireValueCopyButConstructorRuleCannot(bool readOnlyGetter, bool expected)
    {
        var slot = new Register(null, "stack_-16"); var x0 = new Register(null, "X0");
        var address = new Instruction(0, OpCode.Move, x0, new AddressOf(slot));
        var copy = new Instruction(1, OpCode.Move, slot, new Register(null, "X8")) { NativeWriteSize = 8 };
        var call = new Instruction(2, OpCode.Call, new Immediate(0x1000), x0, x0);
        var block = new Block { Instructions = [address, copy, call] };
        Assert.That(NativeNullableConstructorRecovery.ScheduleStackReceiver(block, call,
            requireZeroInitialization: !readOnlyGetter), Is.EqualTo(expected));
        Assert.That(block.Instructions[0], Is.SameAs(expected ? copy : address));
    }

    [TestCase("valid", true)]
    [TestCase("partial-zero", false)]
    [TestCase("nonzero", false)]
    [TestCase("no-init", false)]
    [TestCase("pointer-read", false)]
    [TestCase("pointer-deref", false)]
    [TestCase("intervening-call", false)]
    [TestCase("not-stack", false)]
    public void PureStackAddressMayMoveOnlyAcrossProvenInitializationAndNoPointerUse(string shape, bool expected)
    {
        var slot = new Register(null, shape == "not-stack" ? "X19" : "stack_-16");
        var x0 = new Register(null, "X0");
        var address = new Instruction(0, OpCode.Move, x0, new AddressOf(slot));
        var zero = new Instruction(1, OpCode.Move, slot, new Immediate(shape == "nonzero" ? 1 : 0))
            { NativeWriteSize = shape == "partial-zero" ? 4 : 8 };
        var call = new Instruction(4, OpCode.Call, new Immediate(0x1000), x0, x0, new Register(null, "X1"), new Register(null, "X2"));
        var block = new Block { Instructions = [address] };
        if (shape != "no-init") block.Instructions.Add(zero);
        if (shape == "pointer-read") block.Instructions.Add(new(2, OpCode.Move, new Register(null, "X3"), x0));
        if (shape == "pointer-deref") block.Instructions.Add(new(2, OpCode.Move, new Register(null, "X3"), new MemoryOperand(x0)));
        if (shape == "intervening-call") block.Instructions.Add(new(2, OpCode.CallVoid, new Immediate(0x2000)));
        block.Instructions.Add(call);
        var before = block.Instructions.ToArray();
        Assert.That(NativeNullableConstructorRecovery.ScheduleStackReceiver(block, call), Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(block.Instructions, Is.EqualTo(new[] { zero, address, call }));
            Assert.That(zero.Operands[1], Is.EqualTo(new Immediate(0)));
        }
        else Assert.That(block.Instructions, Is.EqualTo(before));
    }

    [TestCase("direct", true)]
    [TestCase("pointer-copy", true)]
    [TestCase("stale-tail-info", true)]
    [TestCase("missing-info", false)]
    [TestCase("wrong-slot", false)]
    [TestCase("object-receiver", false)]
    [TestCase("live-result", false)]
    [TestCase("wide-enum", false)]
    [TestCase("open", false)]
    [TestCase("virtual", false)]
    public void ProvenBodyStillRequiresExactMetadataLayoutArgumentSlotAndStorage(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var assembly = types.SystemObjectType.DeclaringAssembly;
        var enumeration = new InjectedTypeAnalysisContext(assembly, "Test", "Result",
            assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public)
            { EnumUnderlyingType = shape == "wide-enum" ? types.SystemInt64Type : types.SystemInt32Type };
        enumeration.Fields.Add(new InjectedFieldAnalysisContext("value__", enumeration.EnumUnderlyingType!, FieldAttributes.Public, enumeration));
        var nullable = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Nullable`1");
        var definition = nullable.Methods.Single(m => m.Name == ".ctor");
        var ctor = new ConcreteGenericMethodAnalysisContext(definition,
            shape == "open" ? nullable.GenericParameters : [enumeration], []);
        var slot = new LocalVariable("storage", new(null, "stack_-16"));
        var pointer = new LocalVariable("pointer", new(null, "X0"));
        var result = new LocalVariable("unused_result", new(null, "X0_result"));
        var value = new LocalVariable("value", new(null, "X1"), enumeration);
        var info = new RuntimeMethodInfoAnalysisContext(ctor, assembly);
        IOperand receiver = shape == "object-receiver" ? new LocalVariable("obj", new(null, "X0"), types.SystemObjectType)
            : shape == "pointer-copy" ? pointer : new AddressOf(slot);
        var call = new Instruction(1, OpCode.Call, new Immediate(0x1234), result, receiver, value,
            shape == "missing-info" ? new Immediate(0) : info);
        if (shape == "wrong-slot") call.SetOperands(new Immediate(0x1234), result, receiver, info, value);
        if (shape == "stale-tail-info") call.AddOperands([new RuntimeMethodInfoAnalysisContext(definition, assembly)]);
        call.NativeVirtualDispatch = shape == "virtual";
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        caller.ControlFlowGraph = new([new(0, OpCode.Move, pointer, new AddressOf(slot)), call,
            shape == "live-result" ? new(2, OpCode.Return, result) : new Instruction(2, OpCode.Return)]);
        var operands = call.Operands.ToArray();
        Assert.That(NativeNullableConstructorRecovery.TryResolve(caller, call), Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(call.Operands[0], Is.SameAs(ctor));
            Assert.That(call.Operands.Count, Is.EqualTo(5));
            Assert.That(call.Operands[2], Is.SameAs(receiver));
            Assert.That(call.Operands[3], Is.SameAs(value));
        }
        else Assert.That(call.Operands.ToArray(), Is.EqualTo(operands));
    }

    [Test]
    public void EntireInspectedBodyIsRequired()
    {
        var body = System.Convert.FromHexString("e803003208100039010000b9c0035fd6");
        Assert.That(NativeNullableConstructorRecovery.MatchesBody(body), Is.True);
        for (var at = 0; at < body.Length; at++)
        {
            var changed = (byte[])body.Clone(); changed[at] ^= 1;
            Assert.That(NativeNullableConstructorRecovery.MatchesBody(changed), Is.False, "byte " + at);
        }
        Assert.That(NativeNullableConstructorRecovery.MatchesBody(body.AsSpan(0, 12)), Is.False);
    }
}
