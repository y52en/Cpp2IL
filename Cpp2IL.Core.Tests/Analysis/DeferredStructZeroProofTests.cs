using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DeferredStructZeroProofTests
{
    [TestCase("complete", true)]
    [TestCase("reordered", true)]
    [TestCase("gap", false)]
    [TestCase("call", false)]
    [TestCase("clobber", false)]
    [TestCase("read", false)]
    [TestCase("short-register", false)]
    public void DestinationUsesItsOwnTypeOnlyWithCompleteOriginalZeroCoverage(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var types = app.SystemTypes;
        var date = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.DateTime");
        var vector = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Vector3");
        var rawZero = new Register(null, "X8");
        var define = new Instruction(0, OpCode.Move, rawZero, new Immediate(0))
            { NativeZeroSize = shape == "short-register" ? 4 : 8 };
        var root = new Instruction(1, OpCode.Move, new Register(null, "stack_-60"), rawZero)
            { NativeWriteSize = 8 };
        var tail = new Instruction(2, OpCode.Move,
            new Register(null, shape == "gap" ? "stack_-54" : "stack_-58"), new Immediate(0))
            { NativeWriteSize = 4 };
        var instructions = new List<Instruction> { define };
        if (shape == "clobber") instructions.Add(new(3, OpCode.Move, rawZero, new Immediate(1)));
        if (shape == "reordered") instructions.Add(tail);
        instructions.Add(root);
        if (shape == "call") instructions.Add(new(4, OpCode.CallVoid, new Immediate(123)));
        if (shape == "read") instructions.Add(new(5, OpCode.Move, new Register(null, "X0"), root.Operands[0]));
        if (shape != "reordered") instructions.Add(tail);
        var graph = new ISILControlFlowGraph(instructions);
        WholeStructInitializationRecovery.MarkZeroExtents(graph);
        Assert.That(root.NativeZeroSize >= 12, Is.EqualTo(expected), "raw byte union is proved before managed typing");

        // Later type inference can give the shared zero register an unrelated
        // eight-byte aggregate type. Its partial store is not that aggregate.
        var zero = new LocalVariable("zero", rawZero, date);
        var destination = new LocalVariable("vector", new Register(null, "stack_-60"), vector);
        define.SetOperands(zero, new DefaultStructValue(date));
        root.SetOperands(destination, zero);
        var method = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = graph };
        Assert.That(TypedStructZeroRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        if (expected)
        {
            Assert.That(root.Operands[1], Is.TypeOf<DefaultStructValue>());
            Assert.That(((DefaultStructValue)root.Operands[1]).Type, Is.SameAs(vector));
            Assert.That(TypedStructZeroRecovery.Run(method), Is.Zero, "recovery is idempotent");
        }
        else Assert.That(root.Operands[1], Is.SameAs(zero), "incomplete physical stores remain untouched");
        Assert.That(((DefaultStructValue)define.Operands[1]).Type, Is.SameAs(date), "shared source is not retagged");
    }
}
