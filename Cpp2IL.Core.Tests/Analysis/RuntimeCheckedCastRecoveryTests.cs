using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RuntimeCheckedCastRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("wrong-helper", false)]
    [TestCase("wrong-source", false)]
    [TestCase("wrong-target", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("wrong-width", false)]
    [TestCase("wrong-null-source", false)]
    [TestCase("wrong-null-polarity", false)]
    [TestCase("unknown-source", false)]
    [TestCase("unanchored-source", false)]
    [TestCase("reassigned-source", false)]
    [TestCase("value-target", false)]
    [TestCase("extra-failure-call", false)]
    [TestCase("extra-guard-call", false)]
    [TestCase("escaping-metadata", false)]
    [TestCase("nested-escaping-metadata", false)]
    [TestCase("escaping-flag", false)]
    [TestCase("shared-failure", false)]
    [TestCase("shared-success", false)]
    [TestCase("different-throw", false)]
    [TestCase("extra-transport-call", false)]
    public void OnlyExactNonNullRuntimeCastTransportIsRemoved(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var exceptionType = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.InvalidCastException");
        var nullType = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.NullReferenceException");
        LocalVariable Local(string n, TypeAnalysisContext? type = null) => new(n, new(null, n), type);
        var source = Local("source", t.SystemObjectType); var other = Local("other", t.SystemObjectType);
        TypeAnalysisContext target = shape == "value-target" ? t.SystemInt32Type : new SzArrayTypeAnalysisContext(t.SystemStringType);
        var result = Local("result", target); var flag = Local("flag", t.SystemBooleanType);
        var nullFlag = Local("nullFlag", t.SystemBooleanType); var klass = Local("klass"); var name = Local("name");
        var message = Local("message"); var exception = Local("exception", exceptionType);
        var cfg = new ISILControlFlowGraph([]);
        var before = new Block { ID = 20 }; var guard = new Block { ID = 21 }; var failure = new Block { ID = 22 };
        var success = new Block { ID = 23 }; var transport = new Block { ID = 24 }; var nullExit = new Block { ID = 25 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, before, guard, failure, success, transport, nullExit];
        foreach (var b in cfg.Blocks) { b.Predecessors.Clear(); b.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, before); Edge(before, guard); Edge(before, nullExit);
        Edge(guard, failure); Edge(guard, success); Edge(failure, transport);
        Edge(transport, cfg.ExitBlock); Edge(success, cfg.ExitBlock); Edge(nullExit, cfg.ExitBlock);
        before.Instructions = [new(0, OpCode.CheckEqual, nullFlag, source, new Immediate(0)), new(1, OpCode.ConditionalJump, nullExit, nullFlag)];
        guard.Instructions = [new(2, OpCode.IsInst, result, target, source), new(3, OpCode.CheckEqual, flag, result, new Immediate(0)), new(4, OpCode.ConditionalJump, failure, flag)];
        failure.Instructions = [new(5, OpCode.Move, klass, new MemoryOperand(source)) { NativeReadSize = 8 },
            new(6, OpCode.Move, name, new MemoryOperand(klass, addend: 0x40)) { NativeReadSize = 8 },
            new(7, OpCode.Call, new Immediate(0x1234), message, name, target), new(8, OpCode.Newobj, exception, exceptionType)];
        transport.Instructions = [new(9, OpCode.Throw, exception)];
        nullExit.Instructions = [new(10, OpCode.Throw, nullType)];
        success.Instructions = [new(11, OpCode.Return, result)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", target, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [source, other], Locals = [source, other, result, flag, nullFlag, klass, name, message, exception] };
        if (shape == "wrong-source") failure.Instructions[0].SetOperand(1, new MemoryOperand(other));
        if (shape == "wrong-target") failure.Instructions[2].SetOperand(3, t.SystemObjectType);
        if (shape == "wrong-offset") failure.Instructions[1].SetOperand(1, new MemoryOperand(klass, addend: 0x48));
        if (shape == "wrong-width") failure.Instructions[0].NativeReadSize = 4;
        if (shape == "wrong-null-source") before.Instructions[0].SetOperand(1, other);
        if (shape == "wrong-null-polarity") before.Instructions[0].OpCode = OpCode.CheckNotEqual;
        if (shape == "unknown-source") source.Type = null;
        if (shape == "unanchored-source") method.ParameterLocals = [other];
        if (shape == "reassigned-source") success.Instructions.Insert(0, new(12, OpCode.Move, source, other));
        if (shape == "extra-failure-call") failure.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "extra-guard-call") guard.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "escaping-metadata") success.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("observe"), name));
        if (shape == "nested-escaping-metadata") success.Instructions.Insert(0, new(12, OpCode.Move, other, new MemoryOperand(name)));
        if (shape == "escaping-flag") success.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("observe"), flag));
        if (shape == "shared-failure") Edge(before, failure);
        if (shape == "shared-success") Edge(before, success);
        if (shape == "different-throw") transport.Instructions[0].SetOperand(0, source);
        if (shape == "extra-transport-call") transport.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("cleanup")));
        foreach (var b in cfg.Blocks) b.CalculateBlockType();
        var original = cfg.Instructions.ToArray();
        Assert.That(RuntimeCheckedCastRecovery.TryRecover(method, guard, address => shape != "wrong-helper" && address == 0x1234), Is.EqualTo(expected));
        if (!expected) Assert.That(cfg.Instructions, Is.EqualTo(original));
        else
        {
            Assert.That(guard.Instructions[0].OpCode, Is.EqualTo(OpCode.CastClass));
            Assert.That(guard.Instructions.Last().Operands[0], Is.SameAs(success));
            Assert.That(before.Instructions.Last().Operands[0], Is.SameAs(nullExit));
            Assert.That(nullExit.Instructions[0].Operands[0], Is.SameAs(nullType));
        }
    }
}
