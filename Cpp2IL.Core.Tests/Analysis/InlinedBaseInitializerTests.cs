using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlinedBaseInitializerTests
{
    [TestCase(0, "valid", true)]
    [TestCase(1, "valid", true)]
    [TestCase(2, "valid", true)]
    [TestCase(1, "own-prefix", true)]
    [TestCase(1, "own-suffix", true)]
    [TestCase(1, "wrong-value", false)]
    [TestCase(1, "wrong-width", false)]
    [TestCase(1, "wrong-field", false)]
    [TestCase(1, "wrong-order", false)]
    [TestCase(1, "missing-store", false)]
    [TestCase(1, "callback-inside", false)]
    [TestCase(1, "extra-store-inside", false)]
    [TestCase(1, "unmatched-parent-prefix", false)]
    [TestCase(1, "unknown-memory-prefix", false)]
    [TestCase(1, "wrong-target", false)]
    [TestCase(1, "wrong-receiver", false)]
    [TestCase(1, "virtual-call", false)]
    [TestCase(1, "duplicate-constructor-call", false)]
    [TestCase(1, "reassigned-this", false)]
    [TestCase(1, "implicit-clobber", false)]
    [TestCase(1, "ambiguous-template", false)]
    [TestCase(1, "not-constructor", false)]
    [TestCase(1, "wrong-parent", false)]
    public void CollapseOnlyTheCompleteImmediateParentInitialization(int basePosition, string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var root = app.SystemTypes.SystemObjectType;
        var parent = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Test", "Parent", root, TypeAttributes.Public);
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Test", "Child", parent, TypeAttributes.Public);
        var first = parent.InjectFieldContext("First", app.SystemTypes.SystemInt32Type, FieldAttributes.Private); first.Offset = 16;
        var second = parent.InjectFieldContext("Second", app.SystemTypes.SystemInt32Type, FieldAttributes.Private); second.Offset = 20;
        var own = owner.InjectFieldContext("Own", app.SystemTypes.SystemInt32Type, FieldAttributes.Public); own.Offset = 24;
        var ancestor = root.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        ancestor.PutExtraData(TrivialConstructorRecovery.ObjectProofKey, new TrivialConstructorRecovery.ObjectProof(true));
        var constructor = parent.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public);
        var parentThis = new LocalVariable("parentThis", new(null, "parentThis"), parent) { IsThis = true };
        constructor.ParameterLocals = [parentThis];
        Instruction Store(FieldAnalysisContext field, LocalVariable self, int value) =>
            new(1, OpCode.Move, new FieldReference(field, self, field.Offset), new Immediate(value)) { NativeWriteSize = 4 };
        var native = new List<Instruction> { Store(first, parentThis, 8), Store(second, parentThis, 9) };
        native.Insert(basePosition, new(2, OpCode.CallVoid, ancestor, parentThis)); native.Add(new(3, OpCode.Return));
        constructor.ControlFlowGraph = new(native);
        var template = ConstantFieldConstructorRecovery.Extract(constructor);
        Assert.That(template, Is.Not.Null);
        parent.PutExtraData(ConstantFieldConstructorRecovery.CacheKey,
            shape == "ambiguous-template" ? new[] { template, template } : new[] { template });
        var caller = owner.InjectMethodContext(shape == "not-constructor" ? "Caller" : ".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public);
        var self = new LocalVariable("this", new(null, "this"), owner) { IsThis = true };
        var other = new LocalVariable("other", new(null, "other"), owner);
        caller.ParameterLocals = [self]; caller.Locals = [self, other];
        var one = Store(first, self, 8); var two = Store(second, self, 9);
        var call = new Instruction(4, OpCode.CallVoid, ancestor, self);
        var body = new List<Instruction> { one, two }; body.Insert(basePosition, call);
        if (shape == "own-prefix") body.Insert(0, Store(own, self, 10));
        if (shape == "own-suffix") body.Add(Store(own, self, 10));
        if (shape == "wrong-value") one.SetOperand(1, new Immediate(99));
        if (shape == "wrong-width") one.NativeWriteSize = 8;
        if (shape == "wrong-field") one.SetOperand(0, new FieldReference(own, self, own.Offset));
        if (shape == "wrong-order") { body.Remove(call); body.Insert(0, call); }
        if (shape == "missing-store") body.Remove(one);
        if (shape == "callback-inside") body.Insert(1, new(5, OpCode.CallVoid, new StringLiteral("observable")));
        if (shape == "extra-store-inside") body.Insert(1, Store(first, self, 8));
        if (shape == "unmatched-parent-prefix") body.Insert(0, Store(second, self, 99));
        if (shape == "unknown-memory-prefix") body.Insert(0, new(7, OpCode.Move, new MemoryOperand(self, addend: 16), new Immediate(8)) { NativeWriteSize = 4 });
        if (shape == "wrong-target") call.SetOperand(0, constructor);
        if (shape == "wrong-receiver") call.SetOperand(1, other);
        if (shape == "virtual-call") call.NativeVirtualDispatch = true;
        if (shape == "duplicate-constructor-call") body.Add(new(5, OpCode.CallVoid, ancestor, self));
        if (shape == "reassigned-this") body.Insert(0, new(5, OpCode.Move, self, other));
        if (shape == "implicit-clobber") body.Insert(0, new(5, OpCode.Nop) { ImplicitDefinition = self.Register });
        if (shape == "wrong-parent") owner.BaseType = root;
        body.Add(new(6, OpCode.Return)); caller.ControlFlowGraph = new(body);
        var before = caller.ControlFlowGraph.Instructions.Select(i => i.ToString()).ToArray();
        Assert.That(ConstantFieldConstructorRecovery.RecoverBaseInitializer(caller), Is.EqualTo(expected ? 1 : 0));
        if (expected)
        {
            Assert.That(call.Operands[0], Is.SameAs(constructor));
            Assert.That(one.OpCode, Is.EqualTo(OpCode.Nop)); Assert.That(two.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(first.Visibility, Is.EqualTo(FieldAttributes.Private), "never widen inherited field visibility");
        }
        else Assert.That(caller.ControlFlowGraph.Instructions.Select(i => i.ToString()), Is.EqualTo(before), "no partial prefix mutation");
    }
}
