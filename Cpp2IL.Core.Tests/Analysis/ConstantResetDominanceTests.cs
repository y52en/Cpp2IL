using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstantResetDominanceTests
{
    [TestCase("reset-first", "reset")]
    [TestCase("reset-last", "reset")]
    [TestCase("two-setters", "reset")]
    [TestCase("reversed-stores", "reset")]
    [TestCase("negative-zero", "setter")]
    [TestCase("two-resets", "none")]
    [TestCase("two-setters-only", "none")]
    [TestCase("different-length", "none")]
    [TestCase("disabled", "none")]
    [TestCase("class-initializer", "none")]
    [TestCase("finalizer", "none")]
    [TestCase("readonly", "none")]
    [TestCase("reference", "none")]
    [TestCase("unknown-width", "none")]
    [TestCase("side-effect", "none")]
    public void OnlyOneFullyProvenLiteralResetDominatesEquivalentParameterizedSetters(string shape, string expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "ResetOwner", t.SystemObjectType, TypeAttributes.Public);
        var aType = shape == "reference" ? t.SystemObjectType : t.SystemSingleType;
        var a = owner.InjectFieldContext("value", aType, FieldAttributes.Private | (shape == "readonly" ? FieldAttributes.InitOnly : 0)); a.Offset = 16;
        var b = owner.InjectFieldContext("count", t.SystemInt32Type, FieldAttributes.Private); b.Offset = 24;
        var reset = owner.InjectMethodContext("UnrelatedNameA", t.SystemVoidType, MethodAttributes.Public);
        var setter = owner.InjectMethodContext("UnrelatedNameB", t.SystemVoidType, MethodAttributes.Public, aType, t.SystemInt32Type);
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var p = new LocalVariable("p", new Register(null, "p"), aType);
        var q = new LocalVariable("q", new Register(null, "q"), t.SystemInt32Type);
        reset.ParameterLocals = [self]; setter.ParameterLocals = [self, p, q];
        IOperand constant = shape == "reference" ? new Immediate(0) : new FloatLiteral(0f);
        var widthA = shape == "reference" ? 8 : 4; var widthB = shape == "unknown-width" ? 0 : 4;
        var resetInstructions = new List<Instruction> { new(0, OpCode.Move, new FieldReference(a, self, a.Offset), constant) { NativeWriteSize = widthA } };
        if (shape != "different-length") resetInstructions.Add(new(1, OpCode.Move, new FieldReference(b, self, b.Offset), new Immediate(0)) { NativeWriteSize = widthB });
        resetInstructions.Add(new(2, OpCode.Return)); reset.ControlFlowGraph = new(resetInstructions);
        setter.ControlFlowGraph = new([new(0, OpCode.Move, new FieldReference(a, self, a.Offset), p) { NativeWriteSize = widthA },
            new(1, OpCode.Move, new FieldReference(b, self, b.Offset), q) { NativeWriteSize = widthB }, new(2, OpCode.Return)]);
        var constantTemplate = InlinedFieldMethodRecovery.Extract(reset); var setterTemplate = InlinedFieldMethodRecovery.Extract(setter);
        Assert.That(constantTemplate, Is.Not.Null); Assert.That(setterTemplate, Is.Not.Null);
        var templates = new List<InlinedFieldMethodRecovery.Template> { constantTemplate!, setterTemplate! };
        if (shape == "reset-last") templates.Reverse();
        if (shape == "two-setters") templates.Add(setterTemplate!);
        if (shape == "two-resets") templates.Add(constantTemplate!);
        if (shape == "two-setters-only") templates = [setterTemplate!, setterTemplate!];
        owner.PutExtraData(InlinedFieldMethodRecovery.CacheKey, templates.ToArray());
        if (shape == "class-initializer") owner.InjectMethodContext(".cctor", t.SystemVoidType, MethodAttributes.Static);
        if (shape == "finalizer") owner.InjectMethodContext("Finalize", t.SystemVoidType, MethodAttributes.Family);
        var caller = owner.InjectMethodContext("Caller", t.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
        var receiver = new LocalVariable("receiver", new Register(null, "obj"), owner);
        IOperand actual = shape == "negative-zero" ? new FloatLiteral(BitConverter.Int32BitsToSingle(unchecked((int)0x80000000u))) : constant;
        var first = new Instruction(5, OpCode.Move, new FieldReference(a, receiver, a.Offset), actual) { NativeWriteSize = widthA };
        var second = new Instruction(6, OpCode.Move, new FieldReference(b, receiver, b.Offset), new Immediate(0)) { NativeWriteSize = 4 };
        var stores = shape == "reversed-stores" ? new[] { second, first } : new[] { first, second };
        var instructions = new List<Instruction>(stores);
        if (shape == "side-effect") instructions.Insert(1, new(8, OpCode.CallVoid, new StringLiteral("effect")));
        instructions.Add(new(7, OpCode.Return)); caller.ControlFlowGraph = new(instructions);
        var snapshot = instructions.ToDictionary(i => i, i => (i.OpCode, Args: i.Operands.ToArray()));
        Assert.That(InlinedFieldMethodRecovery.Recover(caller, shape != "disabled"), Is.EqualTo(expected == "none" ? 0 : 1));
        if (expected == "none")
        {
            foreach (var instruction in instructions)
            {
                Assert.That(instruction.OpCode, Is.EqualTo(snapshot[instruction].OpCode));
                Assert.That(instruction.Operands, Is.EqualTo(snapshot[instruction].Args));
            }
        }
        else
        {
            Assert.That(stores[0].Operands[0], Is.SameAs(expected == "reset" ? reset : setter));
            Assert.That(stores[0].Operands.Count, Is.EqualTo(expected == "reset" ? 2 : 4));
            if (expected == "setter") Assert.That(BitConverter.SingleToInt32Bits(((FloatLiteral)stores[0].Operands[2]).Value), Is.EqualTo(unchecked((int)0x80000000u)));
            Assert.That(stores[1].OpCode, Is.EqualTo(OpCode.Nop));
        }
    }
}
