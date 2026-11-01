using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DominatedCastProofTests
{
    [TestCase("valid", true)]
    [TestCase("not-equal", true)]
    [TestCase("cast-not-dominating", false)]
    [TestCase("guard-bypass", false)]
    [TestCase("wrong-target", false)]
    [TestCase("wrong-input", false)]
    [TestCase("null-polarity", false)]
    [TestCase("nonthrowing-null", false)]
    [TestCase("custom-null-throw", false)]
    [TestCase("null-callback", false)]
    [TestCase("predicate-clobber", false)]
    [TestCase("source-reassigned", false)]
    [TestCase("input-reassigned", false)]
    [TestCase("unknown-input", false)]
    public void PriorCastAloneNeverProvesNullSafety(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var nullType = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.NullReferenceException");
        LocalVariable Local(string n, TypeAnalysisContext type) => new(n, new(null, n), type);
        var input = Local("input", t.SystemObjectType); var other = Local("other", t.SystemObjectType);
        var source = Local("cast", t.SystemStringType); var flag = Local("flag", t.SystemBooleanType);
        var cfg = new ISILControlFlowGraph([]);
        var guard = new Block { ID = 20 }; var castBlock = new Block { ID = 21 };
        var depth = new Block { ID = 22 }; var nullExit = new Block { ID = 23 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, guard, castBlock, depth, nullExit];
        foreach (var block in cfg.Blocks) { block.Successors.Clear(); block.Predecessors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, guard); Edge(guard, castBlock); Edge(guard, nullExit);
        Edge(castBlock, depth); Edge(depth, cfg.ExitBlock); Edge(nullExit, cfg.ExitBlock);
        guard.Instructions = [new(0, OpCode.CheckEqual, flag, input, new Immediate(0)), new(1, OpCode.ConditionalJump, nullExit, flag)];
        castBlock.Instructions = [new(2, OpCode.CastClass, source, t.SystemStringType, input), new(3, OpCode.Jump, depth)];
        depth.Instructions = [new(4, OpCode.Return, source)];
        nullExit.Instructions = [new(5, OpCode.Throw, nullType)];
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemStringType,
            MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [input, other], Locals = [input, other, source, flag] };
        if (shape == "not-equal") { guard.Instructions[0].OpCode = OpCode.CheckNotEqual; guard.Instructions[^1].SetOperand(0, castBlock); }
        if (shape == "cast-not-dominating") Edge(guard, depth);
        if (shape == "guard-bypass") Edge(cfg.EntryBlock, castBlock);
        if (shape == "wrong-target") castBlock.Instructions[0].SetOperand(1, t.SystemObjectType);
        if (shape == "wrong-input") guard.Instructions[0].SetOperand(1, other);
        if (shape == "null-polarity") guard.Instructions[0].OpCode = OpCode.CheckNotEqual;
        if (shape == "nonthrowing-null") nullExit.Instructions = [new(5, OpCode.Return, input)];
        if (shape == "custom-null-throw") nullExit.Instructions[0].SetOperand(0, t.SystemObjectType);
        if (shape == "null-callback") nullExit.Instructions.Insert(0, new(6, OpCode.CallVoid, new Immediate(1234)));
        if (shape == "predicate-clobber") guard.Instructions.Insert(1, new(6, OpCode.Move, flag, new Immediate(0)));
        if (shape == "source-reassigned") depth.Instructions.Insert(0, new(6, OpCode.Move, source, other));
        if (shape == "input-reassigned") depth.Instructions.Insert(0, new(6, OpCode.Move, input, other));
        if (shape == "unknown-input") input.Type = null;
        var defs = cfg.Instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var match = new InlineClassCastRecovery.Match(depth, depth, nullExit, cfg.ExitBlock, source, t.SystemStringType);
        var before = cfg.Instructions.ToArray();
        Assert.That(InlineClassCastRecovery.HasDominatingNonNullCast(method, match, defs), Is.EqualTo(expected));
        Assert.That(cfg.Instructions, Is.EqualTo(before));
    }
}
