using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64AtomicReferenceProofTests
{
    private static void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }

    private static (MethodAnalysisContext Method, Instruction Atomic, Instruction NullCheck, Instruction ClassCheck,
        Instruction ClassLoad, Instruction ComparandPhi, Instruction ValuePhi, LocalVariable Broad,
        Block Success, Block Loop, Block Klass) Fixture()
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "AtomicGuardedLoop",
            types.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);
        var initial = Local("initial", types.SystemStringType);
        var broad = Local("broad", types.SystemObjectType);
        var current = Local("current", types.SystemObjectType);
        var value = Local("value", types.SystemObjectType);
        var old = Local("old", types.SystemObjectType);
        var nullFlag = Local("nullFlag", types.SystemBooleanType);
        var klassValue = Local("klassValue", new RuntimeClassTypeAnalysisContext(types.SystemObjectType, types.SystemObjectType.DeclaringAssembly));
        var typeFlag = Local("typeFlag", types.SystemBooleanType);
        var retryFlag = Local("retryFlag", types.SystemBooleanType);
        var graph = new ISILControlFlowGraph([]);
        graph.EntryBlock.Successors.Clear(); graph.ExitBlock.Predecessors.Clear();
        var init = new Block { ID = 2 }; var loop = new Block { ID = 3 };
        var klass = new Block { ID = 4 }; var failure = new Block { ID = 5 }; var success = new Block { ID = 6 };
        graph.Blocks.AddRange([init, loop, klass, failure, success]);
        Edge(graph.EntryBlock, init); Edge(init, loop);
        Edge(loop, success); Edge(loop, klass); Edge(klass, success); Edge(klass, failure);
        Edge(failure, graph.ExitBlock); Edge(success, loop); Edge(success, graph.ExitBlock);
        init.Instructions = [new(0, OpCode.Jump, loop)];
        var comparandPhi = new Instruction(-1, OpCode.Phi, current, initial, old);
        var nullCheck = new Instruction(1, OpCode.CheckEqual, nullFlag, broad, new Immediate(0)) { NativeComparisonSize = 8 };
        loop.Instructions = [comparandPhi, nullCheck, new(2, OpCode.ConditionalJump, success, nullFlag)];
        var classLoad = new Instruction(3, OpCode.Move, klassValue, new MemoryOperand(broad)) { NativeReadSize = 8 };
        var classCheck = new Instruction(4, OpCode.CheckEqual, typeFlag, klassValue, types.SystemStringType) { NativeComparisonSize = 8 };
        klass.Instructions = [classLoad, classCheck, new(5, OpCode.ConditionalJump, success, typeFlag)];
        failure.Instructions = [new(6, OpCode.Throw, types.SystemObjectType)];
        var valuePhi = new Instruction(-1, OpCode.Phi, value, broad, broad);
        var raw = new List<IOperand> { new Immediate(0xACC538), new Register(null, "X0") };
        for (var i = 0; i < 16; i++) raw.Add(new Register(null, i < 8 ? "X" + i : "V" + (i - 8)));
        var atomic = new Instruction(7, OpCode.Call, raw) { NativeDirectCallTarget = 0xACC538 };
        Assert.That(atomic.MarkArm64DirectArgumentSnapshot(), Is.True);
        atomic.SetOperand(1, old);
        atomic.SetOperand(2, Local("location", new ByRefTypeAnalysisContext(types.SystemStringType)));
        atomic.SetOperand(3, value); atomic.SetOperand(4, current);
        success.Instructions = [valuePhi, atomic,
            new(8, OpCode.CheckNotEqual, retryFlag, current, old) { NativeComparisonSize = 8 },
            new(9, OpCode.ConditionalJump, loop, retryFlag)];
        caller.ControlFlowGraph = graph;
        return (caller, atomic, nullCheck, classCheck, classLoad, comparandPhi, valuePhi, broad, success, loop, klass);
    }

    [Test]
    public void EveryGuardedPhiEdgeAndAtomicOldValueBackEdgeProvesAReferenceView()
    {
        var f = Fixture();
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Atomic, true), Is.True);
        var views = f.Success.Instructions.Where(i => i.OpCode == OpCode.CastClass).ToArray();
        Assert.That(views.Length, Is.EqualTo(2));
        Assert.That(views.All(i => ((LocalVariable)i.Operands[0]).Type!.FullName == "System.String"), Is.True);
        Assert.That(f.Broad.Type!.FullName, Is.EqualTo("System.Object"));
        Assert.That(f.Loop.Instructions.Contains(f.NullCheck), Is.True);
        Assert.That(f.Klass.Instructions.Contains(f.ClassCheck), Is.True);
        Assert.That(f.Klass.Instructions.Contains(f.ClassLoad), Is.True);
        Assert.That(f.Klass.Successors.Count, Is.EqualTo(2));
    }

    [TestCase("narrow-null-check")]
    [TestCase("wrong-null-edge")]
    [TestCase("wrong-class")]
    [TestCase("narrow-class-read")]
    [TestCase("narrow-class-comparison")]
    [TestCase("unproven-back-edge")]
    [TestCase("unguarded-phi-edge")]
    [TestCase("duplicate-phi-definition")]
    [TestCase("narrow-copy")]
    public void ReferenceBaseSpellingAloneNeverAuthorizesANarrowing(string shape)
    {
        var f = Fixture(); var types = f.Method.AppContext.SystemTypes;
        switch (shape)
        {
            case "narrow-null-check": f.NullCheck.NativeComparisonSize = 4; break;
            case "wrong-null-edge": f.NullCheck.OpCode = OpCode.CheckNotEqual; break;
            case "wrong-class": f.ClassCheck.SetOperand(2, types.SystemObjectType); break;
            case "narrow-class-read": f.ClassLoad.NativeReadSize = 4; break;
            case "narrow-class-comparison": f.ClassCheck.NativeComparisonSize = 4; break;
            case "unproven-back-edge": f.ComparandPhi.SetOperand(2, f.Broad); break;
            case "unguarded-phi-edge":
                var extra = new Block { ID = 7, Instructions = [new(10, OpCode.Jump, f.Success)] };
                f.Method.ControlFlowGraph!.Blocks.Add(extra);
                Edge(f.Method.ControlFlowGraph.EntryBlock, extra); Edge(extra, f.Success);
                f.ValuePhi.AddOperands([f.Broad]); break;
            case "duplicate-phi-definition":
                f.Success.Instructions.Insert(1, new(-1, OpCode.Move, f.ValuePhi.Destination!, f.Broad) { NativeRegisterCopySize = 8 }); break;
            case "narrow-copy":
                var copy = new LocalVariable("copy", new Register(null, "copy"), types.SystemObjectType);
                f.Success.Instructions.Insert(1, new(11, OpCode.Move, copy, f.ValuePhi.Destination!) { NativeRegisterCopySize = 4 });
                f.Atomic.SetOperand(3, copy); break;
        }
        var before = f.Atomic.Operands.ToArray();
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Atomic, true), Is.False, shape);
        Assert.That(f.Atomic.Operands.ToArray(), Is.EqualTo(before));
        Assert.That(f.Success.Instructions.Any(i => i.OpCode == OpCode.CastClass), Is.False);
    }
}
