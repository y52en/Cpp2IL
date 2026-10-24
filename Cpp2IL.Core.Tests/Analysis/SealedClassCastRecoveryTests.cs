using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SealedClassCastRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("inequality", true)]
    [TestCase("nonnull-branch", true)]
    [TestCase("unsealed", false)]
    [TestCase("value-target", false)]
    [TestCase("unknown-source", false)]
    [TestCase("unanchored-source", false)]
    [TestCase("reassigned-source", false)]
    [TestCase("wrong-helper", false)]
    [TestCase("wrong-width", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("wrong-class", false)]
    [TestCase("wrong-target", false)]
    [TestCase("wrong-null-source", false)]
    [TestCase("wrong-null-polarity", false)]
    [TestCase("extra-guard-call", false)]
    [TestCase("extra-failure-call", false)]
    [TestCase("extra-transport-call", false)]
    [TestCase("extra-null-effect", false)]
    [TestCase("escaping-class", false)]
    [TestCase("escaping-predicate", false)]
    [TestCase("escaping-nested-message", false)]
    [TestCase("shared-failure", false)]
    [TestCase("success-bypass", false)]
    [TestCase("different-throw", false)]
    public void OnlyCompleteSealedClassCastWithNullBypassIsRecovered(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        TypeAnalysisContext target = shape == "unsealed" ? t.SystemObjectType : shape == "value-target" ? t.SystemInt32Type : t.SystemStringType;
        var exceptionType = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.InvalidCastException");
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new(null, name), type);
        var source = Local("source", t.SystemObjectType); var other = Local("other", t.SystemObjectType);
        var klass = Local("klass"); var flag = Local("flag", t.SystemBooleanType);
        var nullFlag = Local("nullFlag", t.SystemBooleanType); var name = Local("name");
        var message = Local("message"); var exception = Local("exception", exceptionType);
        var returned = Local("returned", t.SystemStringType);
        var cfg = new ISILControlFlowGraph([]);
        var before = new Block { ID = 20 }; var guard = new Block { ID = 21 };
        var failure = new Block { ID = 22 }; var transport = new Block { ID = 23 }; var success = new Block { ID = 24 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, before, guard, failure, transport, success];
        foreach (var block in cfg.Blocks) { block.Predecessors.Clear(); block.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, before); Edge(before, guard); Edge(before, success);
        Edge(guard, failure); Edge(guard, success); Edge(failure, transport); Edge(transport, cfg.ExitBlock); Edge(success, cfg.ExitBlock);
        before.Instructions = [new(0, OpCode.CheckEqual, nullFlag, source, new Immediate(0)),
            new(1, OpCode.Move, returned, source), new(2, OpCode.ConditionalJump, success, nullFlag)];
        guard.Instructions = [new(3, OpCode.Move, klass, new MemoryOperand(source)) { NativeReadSize = 8 },
            new(4, OpCode.CheckEqual, flag, klass, target), new(5, OpCode.Move, returned, source),
            new(6, OpCode.ConditionalJump, success, flag)];
        failure.Instructions = [new(7, OpCode.Move, name, new MemoryOperand(klass, addend: 0x40)) { NativeReadSize = 8 },
            new(8, OpCode.Call, new Immediate(0x1234), message, name, target), new(9, OpCode.Newobj, exception, exceptionType)];
        transport.Instructions = [new(10, OpCode.Throw, exception)];
        success.Instructions = [new(11, OpCode.Return, returned)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", target, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [source, other], Locals = [source, other, klass, flag, nullFlag, name, message, exception, returned] };
        if (shape == "inequality") { guard.Instructions[1].OpCode = OpCode.CheckNotEqual; guard.Instructions[^1].SetOperand(0, failure); }
        if (shape == "nonnull-branch") { before.Instructions[0].OpCode = OpCode.CheckNotEqual; before.Instructions[^1].SetOperand(0, guard); }
        if (shape == "unknown-source") source.Type = null;
        if (shape == "unanchored-source") method.ParameterLocals = [other];
        if (shape == "reassigned-source") success.Instructions.Insert(0, new(12, OpCode.Move, source, other));
        if (shape == "wrong-width") guard.Instructions[0].NativeReadSize = 4;
        if (shape == "wrong-offset") failure.Instructions[0].SetOperand(1, new MemoryOperand(klass, addend: 0x48));
        if (shape == "wrong-class") failure.Instructions[0].SetOperand(1, new MemoryOperand(other, addend: 0x40));
        if (shape == "wrong-target") failure.Instructions[1].SetOperand(3, t.SystemObjectType);
        if (shape == "wrong-null-source") before.Instructions[0].SetOperand(1, other);
        if (shape == "wrong-null-polarity") before.Instructions[0].OpCode = OpCode.CheckNotEqual;
        if (shape == "extra-guard-call") guard.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "extra-failure-call") failure.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "extra-transport-call") transport.Instructions.Insert(0, new(12, OpCode.CallVoid, new StringLiteral("cleanup")));
        if (shape == "extra-null-effect") before.Instructions.Insert(1, new(12, OpCode.CallVoid, new StringLiteral("observe")));
        if (shape == "escaping-class") success.Instructions.Insert(0, new(12, OpCode.Return, klass));
        if (shape == "escaping-predicate") success.Instructions.Insert(0, new(12, OpCode.Return, flag));
        if (shape == "escaping-nested-message") success.Instructions.Insert(0, new(12, OpCode.Move, other, new MemoryOperand(message)));
        if (shape == "shared-failure") Edge(before, failure);
        if (shape == "success-bypass") Edge(cfg.EntryBlock, success);
        if (shape == "different-throw") transport.Instructions[0].SetOperand(0, other);
        foreach (var block in cfg.Blocks) block.CalculateBlockType();
        var original = cfg.Instructions.ToArray();
        Assert.That(SealedClassCastRecovery.Recover(method, guard, address => shape != "wrong-helper" && address == 0x1234), Is.EqualTo(expected));
        if (!expected) Assert.That(cfg.Instructions, Is.EqualTo(original));
        else
        {
            Assert.That(cfg.Instructions.Count(i => i.OpCode == OpCode.CastClass), Is.EqualTo(1));
            Assert.That(cfg.Instructions.Any(i => i.OpCode == OpCode.Newobj || i.OpCode == OpCode.Throw), Is.False);
            var cast = cfg.Instructions.Single(i => i.OpCode == OpCode.CastClass);
            Assert.That(cast.Operands[1], Is.SameAs(target)); Assert.That(cast.Operands[2], Is.SameAs(source));
            Assert.That(before.Instructions.IndexOf(cast), Is.LessThan(before.Instructions.FindIndex(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual)));
            Assert.That(cfg.Instructions.Where(i => i.OpCode == OpCode.Move).All(i => ReferenceEquals(i.Operands[1], cast.Operands[0])), Is.True);
        }
    }
}
