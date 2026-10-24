using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedClassTestRecoveryTests
{
    [TestCase("valid", 2)]
    [TestCase("opposite-branches", 2)]
    [TestCase("callback-before-loads", 2)]
    [TestCase("missing-depth-alias-copy", 0)]
    [TestCase("different-ancestor-alias", 0)]
    [TestCase("ancestor-callback", 0)]
    [TestCase("callback-after-loads", 0)]
    [TestCase("callback-after-reload", 1)]
    [TestCase("wrong-class-width", 0)]
    [TestCase("wrong-depth-width", 1)]
    [TestCase("wrong-slot-width", 1)]
    [TestCase("wrong-slot-offset", 1)]
    [TestCase("different-target", 1)]
    [TestCase("escaping-table", 1)]
    [TestCase("source-redefined", 0)]
    [TestCase("wrong-null-object", 0)]
    [TestCase("value-source", 0)]
    [TestCase("byref-source", 0)]
    public void SharedSnapshotsRequireEveryIncomingDefinitionAndPreserveBusinessEffects(string shape, int expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new(null, name), type);
        var obj = Local("obj", types.SystemObjectType); var other = Local("other", types.SystemObjectType);
        if (shape == "value-source") obj.Type = types.SystemInt64Type;
        if (shape == "byref-source") obj.Type = new ByRefTypeAnalysisContext(types.SystemObjectType);
        var classType = new RuntimeClassTypeAnalysisContext(types.SystemObjectType, types.SystemObjectType.DeclaringAssembly);
        var klass = Local("klass", classType); var cachedClass = Local("cachedClass", classType);
        var sd = Local("sharedDepth"); var targetA = Local("targetA", classType); var targetB = Local("targetB", classType);
        var da = Local("depthA"); var db = Local("depthB");
        var tableA = Local("tableA"); var shiftA = Local("shiftA"); var addressA = Local("addressA"); var slotA = Local("slotA");
        var tableB = Local("tableB"); var shiftB = Local("shiftB"); var addressB = Local("addressB"); var slotB = Local("slotB");
        var nullFlag = Local("null", types.SystemBooleanType); var shallowA = Local("shallowA", types.SystemBooleanType);
        var shallowB = Local("shallowB", types.SystemBooleanType); var equalA = Local("equalA", types.SystemBooleanType);
        var equalB = Local("equalB", types.SystemBooleanType); var messageFlag = Local("message", types.SystemBooleanType);
        var graph = new ISILControlFlowGraph([]);
        var guard = new Block { ID = 10 }; var depthA = new Block { ID = 11 }; var ancestorA = new Block { ID = 12 };
        var message = new Block { ID = 13 }; var reload = new Block { ID = 14 }; var depthB = new Block { ID = 15 };
        var ancestorB = new Block { ID = 16 }; var success = new Block { ID = 17 }; var failure = new Block { ID = 18 };
        var nullExit = new Block { ID = 19 };
        graph.Blocks = [graph.EntryBlock, graph.ExitBlock, guard, depthA, ancestorA, message, reload, depthB, ancestorB, success, failure, nullExit];
        foreach (var block in graph.Blocks) { block.Predecessors.Clear(); block.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(graph.EntryBlock, guard); Edge(guard, depthA); Edge(guard, nullExit);
        Edge(depthA, ancestorA); Edge(depthA, depthB); Edge(ancestorA, message); Edge(ancestorA, depthB);
        Edge(message, reload); Edge(message, success); Edge(reload, depthB);
        Edge(depthB, ancestorB); Edge(depthB, failure); Edge(ancestorB, failure); Edge(ancestorB, success);
        Edge(success, graph.ExitBlock); Edge(failure, graph.ExitBlock); Edge(nullExit, graph.ExitBlock);
        guard.Instructions = [new(0, OpCode.CheckEqual, nullFlag, shape == "wrong-null-object" ? other : obj, new Immediate(0)),
            new(1, OpCode.ConditionalJump, nullExit, nullFlag)];
        depthA.Instructions = [
            new(2, OpCode.Move, klass, new MemoryOperand(obj)) { NativeReadSize = shape == "wrong-class-width" ? 4 : 8 },
            new(3, OpCode.Move, targetA, types.SystemStringType),
            new(4, OpCode.Move, sd, new MemoryOperand(klass, addend: 0x120)) { NativeReadSize = 1 },
            new(5, OpCode.Move, da, new MemoryOperand(targetA, addend: 0x120)) { NativeReadSize = shape == "wrong-depth-width" ? 4 : 1 },
            new(6, OpCode.CheckLess, shallowA, sd, da),
            new(-1, OpCode.Move, cachedClass, klass),
            new(7, OpCode.ConditionalJump, depthB, shallowA)];
        ancestorA.Instructions = [
            new(8, OpCode.Move, tableA, new MemoryOperand(klass, addend: 0xC8)) { NativeReadSize = 8 },
            new(9, OpCode.ShiftLeft, shiftA, da, new Immediate(3)), new(10, OpCode.Add, addressA, tableA, shiftA),
            new(11, OpCode.Move, slotA, new MemoryOperand(addressA, addend: shape == "wrong-slot-offset" ? -16 : -8))
                { NativeReadSize = shape == "wrong-slot-width" ? 4 : 8 },
            new(12, OpCode.CheckNotEqual, equalA, slotA, shape == "different-target" ? types.SystemObjectType : types.SystemStringType),
            new(-1, OpCode.Move, cachedClass, klass), new(13, OpCode.ConditionalJump, depthB, equalA)];
        var businessMessage = new Instruction(14, OpCode.Call, new StringLiteral("observable-message"), messageFlag, obj);
        message.Instructions = [businessMessage, new(15, OpCode.ConditionalJump, success, messageFlag)];
        reload.Instructions = [new(16, OpCode.Move, cachedClass, new MemoryOperand(obj)) { NativeReadSize = 8 },
            new(17, OpCode.Move, sd, new MemoryOperand(cachedClass, addend: 0x120)) { NativeReadSize = 1 }];
        depthB.Instructions = [new(18, OpCode.Move, targetB, types.SystemObjectType),
            new(19, OpCode.Move, db, new MemoryOperand(targetB, addend: 0x120)) { NativeReadSize = 1 },
            new(20, OpCode.CheckLess, shallowB, sd, db), new(21, OpCode.ConditionalJump, failure, shallowB)];
        ancestorB.Instructions = [new(22, OpCode.Move, tableB, new MemoryOperand(cachedClass, addend: 0xC8)) { NativeReadSize = 8 },
            new(23, OpCode.ShiftLeft, shiftB, db, new Immediate(3)), new(24, OpCode.Add, addressB, tableB, shiftB),
            new(25, OpCode.Move, slotB, new MemoryOperand(addressB, addend: -8)) { NativeReadSize = 8 },
            new(26, OpCode.CheckEqual, equalB, slotB, types.SystemObjectType), new(27, OpCode.ConditionalJump, success, equalB)];
        var observableSuccess = new Instruction(28, OpCode.CallVoid, new StringLiteral("observable-success"), obj);
        var observableFailure = new Instruction(30, OpCode.CallVoid, new StringLiteral("observable-failure"), obj);
        success.Instructions = [observableSuccess, new(29, OpCode.Return, new Immediate(1))];
        failure.Instructions = [observableFailure, new(31, OpCode.Return, new Immediate(0))];
        nullExit.Instructions = [new(32, OpCode.Return, new Immediate(0))];
        if (shape == "opposite-branches")
        {
            depthA.Instructions[4].OpCode = OpCode.CheckGreaterOrEqual;
            depthA.Instructions[^1].SetOperand(0, ancestorA);
            ancestorA.Instructions[4].OpCode = OpCode.CheckEqual;
            ancestorA.Instructions[^1].SetOperand(0, message);
        }
        if (shape == "missing-depth-alias-copy") depthA.Instructions.RemoveAt(5);
        if (shape == "different-ancestor-alias")
        {
            var otherClass = Local("otherClass", classType);
            depthA.Instructions.Insert(0, new(33, OpCode.Move, otherClass, new MemoryOperand(other)) { NativeReadSize = 8 });
            ancestorA.Instructions[^2].SetOperand(1, otherClass);
        }
        var callback = new Instruction(34, OpCode.CallVoid, new StringLiteral("observable-callback"));
        if (shape == "callback-before-loads") depthA.Instructions.Insert(0, callback);
        if (shape == "callback-after-loads") depthA.Instructions.Insert(4, callback);
        if (shape == "ancestor-callback") ancestorA.Instructions.Insert(0, callback);
        if (shape == "callback-after-reload") reload.Instructions.Add(callback);
        if (shape == "escaping-table") observableFailure.SetOperand(1, tableA);
        if (shape == "source-redefined") success.Instructions.Insert(0, new(35, OpCode.Move, obj, other));
        var method = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemBooleanType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = graph, ParameterLocals = [obj, other] };
        var original = graph.Instructions.ToArray(); var callCount = original.Count(i => i.IsCall);
        Assert.That(SharedClassTestRecovery.Recover(method), Is.EqualTo(expected));
        Assert.That(graph.Instructions.Count(i => i.OpCode == OpCode.IsInst), Is.EqualTo(expected));
        Assert.That(graph.Instructions.Count(i => i.IsCall), Is.EqualTo(callCount));
        foreach (var operation in new[] { businessMessage, observableSuccess, observableFailure })
            Assert.That(graph.Instructions.Contains(operation), Is.True);
        Assert.That(graph.Blocks.Contains(success) && graph.Blocks.Contains(failure) && graph.Blocks.Contains(nullExit), Is.True);
        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.CastClass), Is.False);
        if (expected == 0) Assert.That(graph.Instructions, Is.EqualTo(original));
    }
}
