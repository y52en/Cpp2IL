using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DistinctNullSealedCastTests
{
    [TestCase("valid", true)]
    [TestCase("nonnull-branch", true)]
    [TestCase("inequality", true)]
    [TestCase("both-inverted", true)]
    [TestCase("prefix-effect", true)]
    [TestCase("source-call", true)]
    [TestCase("copy", true)]
    [TestCase("null-throws", true)]
    [TestCase("generic-closed", true)]
    [TestCase("wrong-null-polarity", false)]
    [TestCase("wrong-null-source", false)]
    [TestCase("foreign-branch", false)]
    [TestCase("shared-success", false)]
    [TestCase("effect-after-null-test", false)]
    [TestCase("guard-effect", false)]
    [TestCase("failure-effect", false)]
    [TestCase("transport-effect", false)]
    [TestCase("escaping-class-on-null", false)]
    [TestCase("unsealed", false)]
    [TestCase("value-target", false)]
    [TestCase("wrong-helper", false)]
    [TestCase("wrong-target", false)]
    [TestCase("reassigned-source", false)]
    [TestCase("unknown-source", false)]
    public void DistinctNullControlFlowAndObservableEffectsRemainIntact(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        TypeAnalysisContext target = shape == "unsealed" ? t.SystemObjectType
            : shape == "value-target" ? t.SystemInt32Type : t.SystemStringType;
        if (shape == "generic-closed")
            target = new GenericInstanceTypeAnalysisContext(app.Assemblies.SelectMany(a => a.Types)
                .Single(x => x.FullName == "System.Action`1"), [t.SystemStringType]);
        var invalidCast = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.InvalidCastException");
        LocalVariable Local(string n, TypeAnalysisContext? type = null) => new(n, new(null, n), type);
        var source = Local("source", t.SystemObjectType); var other = Local("other", t.SystemObjectType);
        var klass = Local("klass"); var name = Local("name"); var message = Local("message");
        var flag = Local("flag", t.SystemBooleanType); var nullFlag = Local("nullFlag", t.SystemBooleanType);
        var exception = Local("exception", invalidCast); var copied = Local("copied", t.SystemObjectType);
        var cfg = new ISILControlFlowGraph([]);
        var before = new Block { ID = 20 }; var guard = new Block { ID = 21 };
        var failure = new Block { ID = 22 }; var transport = new Block { ID = 23 };
        var success = new Block { ID = 24 }; var nullPath = new Block { ID = 25 }; var merge = new Block { ID = 26 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, before, guard, failure, transport, success, nullPath, merge];
        foreach (var b in cfg.Blocks) { b.Predecessors.Clear(); b.Successors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, before); Edge(before, guard); Edge(before, nullPath);
        Edge(guard, failure); Edge(guard, success); Edge(failure, transport); Edge(transport, cfg.ExitBlock);
        Edge(success, merge); Edge(nullPath, merge); Edge(merge, cfg.ExitBlock);
        before.Instructions = [new(1, OpCode.CheckEqual, nullFlag, source, new Immediate(0)),
            new(2, OpCode.ConditionalJump, nullPath, nullFlag)];
        guard.Instructions = [new(3, OpCode.Move, klass, new MemoryOperand(source)) { NativeReadSize = 8 },
            new(4, OpCode.CheckEqual, flag, klass, target), new(5, OpCode.ConditionalJump, success, flag)];
        failure.Instructions = [new(6, OpCode.Move, name, new MemoryOperand(klass, addend: 0x40)) { NativeReadSize = 8 },
            new(7, OpCode.Call, new Immediate(0x1234), message, name, target), new(8, OpCode.Newobj, exception, invalidCast)];
        transport.Instructions = [new(9, OpCode.Throw, exception)];
        var nullEffect = new Instruction(10, OpCode.CallVoid, new StringLiteral("null-effect"));
        var nonNullEffect = new Instruction(12, OpCode.CallVoid, new StringLiteral("nonnull-effect"));
        nullPath.Instructions = [nullEffect, new(11, OpCode.Jump, merge)];
        success.Instructions = [nonNullEffect, new(13, OpCode.Jump, merge)];
        merge.Instructions = [new(14, OpCode.Return, source)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [source, other],
                Locals = [source, other, klass, name, message, flag, nullFlag, exception, copied] };
        Instruction Effect(int index) => new(index, OpCode.CallVoid, new StringLiteral("must-preserve"));
        if (shape is "nonnull-branch" or "both-inverted")
        { before.Instructions[0].OpCode = OpCode.CheckNotEqual; before.Instructions[^1].SetOperand(0, guard); }
        if (shape is "inequality" or "both-inverted")
        { guard.Instructions[1].OpCode = OpCode.CheckNotEqual; guard.Instructions[^1].SetOperand(0, failure); }
        if (shape == "prefix-effect") before.Instructions.Insert(0, Effect(0));
        if (shape == "source-call")
        {
            var producer = new InjectedMethodAnalysisContext(t.SystemObjectType, "Produce", t.SystemObjectType,
                MethodAttributes.Public | MethodAttributes.Static, []);
            before.Instructions.Insert(0, new(0, OpCode.Call, producer, source)); method.ParameterLocals = [other];
        }
        if (shape == "copy") guard.Instructions.Insert(2, new(15, OpCode.Move, copied, source));
        if (shape == "null-throws")
        {
            cfg.RemoveEdge(nullPath, merge); Edge(nullPath, cfg.ExitBlock);
            nullPath.Instructions = [nullEffect, new(11, OpCode.Throw,
                app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.NullReferenceException"))];
        }
        if (shape == "wrong-null-polarity") before.Instructions[0].OpCode = OpCode.CheckNotEqual;
        if (shape == "wrong-null-source") before.Instructions[0].SetOperand(1, other);
        if (shape == "foreign-branch") before.Instructions[^1].SetOperand(0, failure);
        if (shape == "shared-success") Edge(cfg.EntryBlock, success);
        if (shape == "effect-after-null-test") before.Instructions.Insert(1, Effect(15));
        if (shape == "guard-effect") guard.Instructions.Insert(2, Effect(15));
        if (shape == "failure-effect") failure.Instructions.Insert(0, Effect(15));
        if (shape == "transport-effect") transport.Instructions.Insert(0, Effect(15));
        if (shape == "escaping-class-on-null") nullPath.Instructions.Insert(0, new(15, OpCode.Return, klass));
        if (shape == "wrong-target") failure.Instructions[1].SetOperand(3, t.SystemObjectType);
        if (shape == "reassigned-source") nullPath.Instructions.Insert(0, new(15, OpCode.Move, source, other));
        if (shape == "unknown-source") source.Type = null;
        foreach (var b in cfg.Blocks) b.CalculateBlockType();
        var original = cfg.Instructions.ToArray(); var nullBody = nullPath.Instructions.ToArray();
        var nullSuccessors = nullPath.Successors.ToArray();
        var effects = cfg.Instructions.Where(i => i.OpCode == OpCode.CallVoid).ToArray();
        Assert.That(SealedClassCastRecovery.Recover(method, guard, a => shape != "wrong-helper" && a == 0x1234), Is.EqualTo(expected));
        if (!expected) { Assert.That(cfg.Instructions, Is.EqualTo(original)); return; }
        var cast = cfg.Instructions.Single(i => i.OpCode == OpCode.CastClass);
        Assert.That(cast.Operands[1], Is.SameAs(target)); Assert.That(cast.Operands[2], Is.SameAs(source));
        Assert.That(before.Instructions.IndexOf(cast), Is.EqualTo(before.Instructions.FindIndex(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual) - 1));
        Assert.That(nullPath.Instructions, Is.EqualTo(nullBody)); Assert.That(nullPath.Successors, Is.EqualTo(nullSuccessors));
        Assert.That(before.Successors, Does.Contain(nullPath)); Assert.That(guard.Successors, Is.EqualTo(new[] { success }));
        Assert.That(cfg.Instructions.Where(i => i.OpCode == OpCode.CallVoid), Is.EqualTo(effects));
        Assert.That(cfg.Blocks, Does.Not.Contain(failure)); Assert.That(cfg.Blocks, Does.Not.Contain(transport));
        Assert.That(merge.Instructions.Single(i => i.OpCode == OpCode.Return).Operands[0], Is.SameAs(cast.Operands[0]));
        if (shape == "source-call") Assert.That(before.Instructions[0].Operands[1], Is.SameAs(source));
    }
}
