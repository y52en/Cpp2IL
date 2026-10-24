using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CastSuccessCopyProofTests
{
    [TestCase("single-edge", true)]
    [TestCase("null-and-success", true)]
    [TestCase("native-pointer-copy", true)]
    [TestCase("nested-field-read", true)]
    [TestCase("wrong-source", false)]
    [TestCase("non-copy", false)]
    [TestCase("narrow-copy", false)]
    [TestCase("unproven-native-width", false)]
    [TestCase("third-write", false)]
    [TestCase("outside-write", false)]
    [TestCase("early-read", false)]
    [TestCase("bypass-read", false)]
    [TestCase("phi-read", false)]
    [TestCase("value-alias", false)]
    [TestCase("pointer-alias", false)]
    [TestCase("parameter-alias", false)]
    [TestCase("source-alias", false)]
    [TestCase("implicit-clobber", false)]
    [TestCase("address-escape", false)]
    [TestCase("early-memory-store", false)]
    public void OnlyIdenticalCopiesWhoseReadsAreAfterProvenSuccessCanSurvive(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        LocalVariable Local(string n, TypeAnalysisContext? type = null) => new(n, new(null, n), type);
        var source = Local("source", t.SystemObjectType);
        var other = Local("other", t.SystemObjectType);
        var alias = Local("alias", t.SystemObjectType);
        var output = Local("output");
        var cfg = new ISILControlFlowGraph([]);
        var guard = new Block { ID = 20 }; var ancestor = new Block { ID = 21 };
        var success = new Block { ID = 22 }; var bypass = new Block { ID = 23 };
        cfg.Blocks = [cfg.EntryBlock, cfg.ExitBlock, guard, ancestor, success, bypass];
        foreach (var block in cfg.Blocks) { block.Successors.Clear(); block.Predecessors.Clear(); }
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, guard); Edge(guard, ancestor); Edge(guard, success);
        Edge(ancestor, success); Edge(success, cfg.ExitBlock); Edge(bypass, cfg.ExitBlock);
        ancestor.Instructions = [new(-1, OpCode.Move, alias, source)];
        guard.Instructions = [];
        success.Instructions = [new(2, OpCode.Return, alias)];
        if (shape == "null-and-success") guard.Instructions.Add(new(-1, OpCode.Move, alias, source));
        if (shape == "native-pointer-copy")
        { ancestor.Instructions[0].Index = 1; ancestor.Instructions[0].NativeRegisterCopySize = 8; }
        if (shape == "nested-field-read") success.Instructions = [new(2, OpCode.Move, output, new MemoryOperand(alias))];
        if (shape == "wrong-source") ancestor.Instructions[0].SetOperand(1, other);
        if (shape == "non-copy") ancestor.Instructions[0].OpCode = OpCode.NumericConvert;
        if (shape == "narrow-copy") ancestor.Instructions[0].NativeRegisterCopySize = 4;
        if (shape == "unproven-native-width") ancestor.Instructions[0].Index = 1;
        if (shape == "third-write")
        { guard.Instructions.Add(new(-1, OpCode.Move, alias, source)); guard.Instructions.Add(new(-1, OpCode.Move, alias, source)); }
        if (shape == "outside-write") success.Instructions.Insert(0, new(-1, OpCode.Move, alias, source));
        if (shape == "early-read") guard.Instructions.Add(new(3, OpCode.CallVoid, new Immediate(1234), alias));
        if (shape == "bypass-read") bypass.Instructions = [new(3, OpCode.Return, alias)];
        if (shape == "phi-read") success.Instructions = [new(2, OpCode.Phi, output, alias, source)];
        if (shape == "value-alias") alias.Type = t.SystemInt32Type;
        if (shape == "pointer-alias") alias.Type = new PointerTypeAnalysisContext(t.SystemObjectType);
        if (shape == "implicit-clobber") success.Instructions.Add(new(4, OpCode.Nop) { ImplicitDefinition = alias.Register });
        if (shape == "address-escape") success.Instructions = [new(4, OpCode.CallVoid, new Immediate(1234), new AddressOf(alias))];
        if (shape == "early-memory-store") guard.Instructions.Add(new(4, OpCode.Move, new MemoryOperand(alias), new Immediate(0)));
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = shape == "parameter-alias" ? [source, other, alias] : [source, other] };
        var match = new InlineClassCastRecovery.Match(guard, ancestor, bypass, success, source, t.SystemStringType);
        var before = cfg.Instructions.Select(i => i.ToString()).ToArray();
        Assert.That(InlineClassCastRecovery.CanPreserveSuccessCopy(method, match, guard, [ancestor], [success],
            source, shape == "source-alias" ? source : alias, new Dictionary<LocalVariable, Instruction>()), Is.EqualTo(expected));
        Assert.That(cfg.Instructions.Select(i => i.ToString()), Is.EqualTo(before), "proof never mutates the graph");
    }
}
