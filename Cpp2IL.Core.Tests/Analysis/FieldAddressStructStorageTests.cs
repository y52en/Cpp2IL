using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class FieldAddressStructStorageTests
{
    [Test]
    public void EscapedStructFieldKeepsTheValueCopySeparateFromItsSource()
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var data = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "AddressedCopy", types.SystemValueTypeType, TypeAttributes.Public);
        var field = data.InjectFieldContext("X", types.SystemInt32Type, FieldAttributes.Public);
        var source = new LocalVariable("source", new Register(null, "source"), data) { ParameterIndex = 0 };
        var copy = new LocalVariable("copy", new Register(null, "copy"), data);
        var copied = new Instruction(0, OpCode.Move, copy, source);
        var address = new FieldReference(field, copy, 0);
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "CopyThenMutateField",
            types.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [data]);
        caller.Locals = [source, copy]; caller.ParameterLocals = [source];
        caller.ControlFlowGraph = new([copied,
            new(1, OpCode.CallVoid, new Immediate(1234), new AddressOf(address)), new(2, OpCode.Return)]);
        DeadCodeEliminator.Run(caller); SsaSimplifier.Run(caller); DeadCodeEliminator.Run(caller);
        CopyCoalescer.Run(caller); Simplifier.Simplify(caller); LocalVariables.RemoveUnused(caller);
        Assert.That(address.Local, Is.SameAs(copy));
        Assert.That(copied.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(copied.Operands[0], Is.SameAs(copy));
        Assert.That(copied.Operands[1], Is.SameAs(source));
        Assert.That(caller.Locals.Contains(copy), Is.True);
    }
}
