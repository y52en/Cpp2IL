using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class DeadCycleEliminationTests
{
    private static LocalVariable L(string name) => new(name, new Register(null, name));

    [Test]
    public void UnobservablePhiCopyCycleDoesNotKeepItselfAlive()
    {
        var a = L("a"); var b = L("b");
        var phi = new Instruction(0, OpCode.Phi, a, b, new Immediate(0));
        var add = new Instruction(1, OpCode.Add, b, a, new Immediate(1));
        var ret = new Instruction(2, OpCode.Return, new Immediate(1));
        var graph = new ISILControlFlowGraph([phi, add, ret]);
        DeadCodeEliminator.Run(graph);
        Assert.That(phi.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(add.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(ret.OpCode, Is.EqualTo(OpCode.Return));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void ObservableValueOrEscapedStorageKeepsItsProducers(bool escaped)
    {
        var a = L("a"); var b = L("b");
        var phi = new Instruction(0, OpCode.Phi, a, b, new Immediate(0));
        var add = new Instruction(1, OpCode.Add, b, a, new Immediate(1));
        IOperand observed = escaped ? new AddressOf(a) : a;
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Observe"), observed);
        var graph = new ISILControlFlowGraph([phi, add, call, new Instruction(3, OpCode.Return)]);
        DeadCodeEliminator.Run(graph);
        Assert.That(phi.OpCode, Is.EqualTo(OpCode.Phi));
        Assert.That(add.OpCode, Is.EqualTo(OpCode.Add));
        Assert.That(call.OpCode, Is.EqualTo(OpCode.CallVoid));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void PotentiallyThrowingOperationsAreNotMadeUnobservable(bool divide)
    {
        var a = L("a"); var b = L("b");
        var phi = new Instruction(0, OpCode.Phi, a, b, new Immediate(0));
        var operation = divide ? new Instruction(1, OpCode.Divide, b, new Immediate(1), a)
            : new Instruction(1, OpCode.Move, b, new MemoryOperand(a));
        var graph = new ISILControlFlowGraph([phi, operation, new Instruction(2, OpCode.Return)]);
        DeadCodeEliminator.Run(graph);
        Assert.That(phi.OpCode, Is.EqualTo(OpCode.Phi));
        Assert.That(operation.OpCode, Is.Not.EqualTo(OpCode.Nop));
    }
}
