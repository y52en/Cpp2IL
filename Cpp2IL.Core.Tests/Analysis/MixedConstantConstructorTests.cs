using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MixedConstantConstructorTests
{
    [TestCase("int")]
    [TestCase("float")]
    [TestCase("double")]
    [TestCase("null")]
    [TestCase("string")]
    public void FullMixedTemplateRequiresExactConstantAndRestoresRealParameter(string shape)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "Mixed", t.SystemObjectType, TypeAttributes.Public);
        var fieldType = shape switch { "float" => t.SystemSingleType, "double" => t.SystemDoubleType,
            "null" or "string" => t.SystemStringType, _ => t.SystemInt32Type };
        IOperand literal = shape switch { "float" => new FloatLiteral(-0f), "double" => new DoubleLiteral(-0d),
            "null" => new Immediate(0), "string" => new StringLiteral("constant"), _ => new Immediate(73) };
        var field = owner.InjectFieldContext("constant", fieldType, FieldAttributes.Public);
        var argumentField = owner.InjectFieldContext("argument", t.SystemStringType, FieldAttributes.Public);
        var ctor = owner.InjectMethodContext(".ctor", t.SystemVoidType, MethodAttributes.Public, t.SystemStringType);
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var parameter = new LocalVariable("input", new Register(null, "input"), t.SystemStringType);
        var objectCtor = t.SystemObjectType.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        ctor.ParameterLocals = [self, parameter]; ctor.Locals = [self, parameter];
        ctor.ControlFlowGraph = new([new(0, OpCode.CallVoid, objectCtor, self),
            new(1, OpCode.Move, new FieldReference(field, self, 16), literal),
            new(2, OpCode.Move, new FieldReference(argumentField, self, 24), parameter), new(3, OpCode.Return)]);
        var template = InlinedConstructorRecovery.Extract(ctor);
        Assert.That(template, Is.Not.Null);
        Assert.That(template!.Assignments[0].Parameter, Is.EqualTo(-1));
        Assert.That(template.Assignments[0].Constant, Is.SameAs(literal));
        var caller = owner.InjectMethodContext("Caller", t.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
        var obj = new LocalVariable("obj", new Register(null, "obj"), owner);
        var allocation = new Instruction(0, OpCode.Newobj, obj, owner);
        var call = new Instruction(1, OpCode.CallVoid, objectCtor, obj);
        var constantStore = new Instruction(2, OpCode.Move, new FieldReference(field, obj, 16), literal);
        var value = new StringLiteral("actual argument");
        var argumentStore = new Instruction(3, OpCode.Move, new FieldReference(argumentField, obj, 24), value);
        caller.ControlFlowGraph = new([allocation, call, constantStore, argumentStore, new(4, OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller, allocation, [template]), Is.True);
        Assert.That(call.Operands[0], Is.SameAs(ctor));
        Assert.That(call.Operands.Count, Is.EqualTo(3), "constant writes are not constructor arguments");
        Assert.That(call.Operands[2], Is.EqualTo(value));
        Assert.That(constantStore.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(argumentStore.OpCode, Is.EqualTo(OpCode.Nop));
    }

    [TestCase("signed-zero")]
    [TestCase("nan-payload")]
    [TestCase("wrong-integer")]
    public void DifferentConstantBitPatternsCannotBeSubstituted(string shape)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "Bits", t.SystemObjectType, TypeAttributes.Public);
        var field = owner.InjectFieldContext("constant", shape == "wrong-integer" ? t.SystemInt32Type : t.SystemSingleType, FieldAttributes.Public);
        var other = owner.InjectFieldContext("value", t.SystemStringType, FieldAttributes.Public);
        var ctor = owner.InjectMethodContext(".ctor", t.SystemVoidType, MethodAttributes.Public, t.SystemStringType);
        IOperand expected = shape == "wrong-integer" ? new Immediate(1) : new FloatLiteral(BitConverter.Int32BitsToSingle(shape == "nan-payload" ? 0x7fc00001 : unchecked((int)0x80000000)));
        IOperand actual = shape == "wrong-integer" ? new Immediate(2) : new FloatLiteral(BitConverter.Int32BitsToSingle(shape == "nan-payload" ? 0x7fc00002 : 0));
        var template = new InlinedConstructorRecovery.Template(ctor, [new(field, -1, expected), new(other, 0)]);
        var caller = owner.InjectMethodContext("Caller", t.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
        var obj = new LocalVariable("obj", new Register(null, "obj"), owner);
        var allocation = new Instruction(0, OpCode.Newobj, obj, owner);
        var objectCtor = t.SystemObjectType.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var call = new Instruction(1, OpCode.CallVoid, objectCtor, obj);
        var store = new Instruction(2, OpCode.Move, new FieldReference(field, obj, 16), actual);
        caller.ControlFlowGraph = new([allocation, call, store,
            new(3, OpCode.Move, new FieldReference(other, obj, 24), new StringLiteral("value")), new(4, OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller, allocation, [template]), Is.False);
        Assert.That(store.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(call.Operands[0], Is.SameAs(objectCtor));
    }
}
