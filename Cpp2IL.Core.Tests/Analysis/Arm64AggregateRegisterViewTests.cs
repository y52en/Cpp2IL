using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64AggregateRegisterViewTests
{
    private static (ISILControlFlowGraph Graph, LocalVariable Root, LocalVariable Value,
        Instruction Compare, List<Instruction> Steps) Fixture(bool high)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var aggregate = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Matrix4x4");
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);
        var root = Local("X0", aggregate);
        var copied = Local("X8", app.SystemTypes.SystemUInt64Type);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "ReturnAggregate", aggregate,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var steps = new List<Instruction>
        {
            new(0, OpCode.Call, target, root),
            new(1, OpCode.Move, copied, root) { NativeRegisterCopySize = 8 }
        };
        var value = copied;
        if (high)
        {
            var input = Local("shift_input", app.SystemTypes.SystemUInt64Type);
            var shifted = Local("shift_result", app.SystemTypes.SystemUInt64Type);
            value = Local("output", app.SystemTypes.SystemUInt64Type);
            var u64 = app.SystemTypes.SystemUInt64Type;
            steps.Add(new(2, OpCode.NumericConvert, input, u64, u64, copied) { NativeArithmeticSize = 8 });
            steps.Add(new(3, OpCode.ShiftRightUnsigned, shifted, input, new Immediate(32)) { NativeArithmeticSize = 8 });
            steps.Add(new(4, OpCode.NumericConvert, value, u64, u64, shifted) { NativeArithmeticSize = 8 });
        }
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var compare = new Instruction(5, OpCode.CheckGreater, flag, value, new Immediate(7)) { NativeComparisonSize = 4 };
        steps.Add(compare);
        var graph = new ISILControlFlowGraph([]);
        graph.EntryBlock.Successors.Clear(); graph.ExitBlock.Predecessors.Clear();
        var body = new Block { ID = 2, Instructions = steps };
        graph.Blocks.Add(body);
        graph.EntryBlock.Successors.Add(body); body.Predecessors.Add(graph.EntryBlock);
        body.Successors.Add(graph.ExitBlock); graph.ExitBlock.Predecessors.Add(body);
        return (graph, root, value, compare, steps);
    }

    private static Dictionary<LocalVariable, Instruction?> Definitions(ISILControlFlowGraph graph) =>
        graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);

    [TestCase(false, 0)]
    [TestCase(true, 4)]
    public void TypedUInt64CopyStillIdentifiesTheExactAggregateByteView(bool high, int expectedOffset)
    {
        var f = Fixture(high);
        var originalOperands = f.Steps.Select(i => i.Operands.ToArray()).ToArray();
        Assert.That(Arm64AggregateReturnLowWordRecovery.TryResolveRegisterView(f.Graph, Definitions(f.Graph), f.Compare,
            f.Value, out var root, out var origin, out var offset), Is.True);
        Assert.That(root, Is.SameAs(f.Root));
        Assert.That(origin, Is.SameAs(f.Steps[0]));
        Assert.That(offset, Is.EqualTo(expectedOffset));
        // Analysis must preserve all producers and their other consumers.
        for (var i = 0; i < f.Steps.Count; i++) Assert.That(f.Steps[i].Operands.ToArray(), Is.EqualTo(originalOperands[i]));
    }

    [TestCase("unknown-copy")]
    [TestCase("narrow-copy")]
    [TestCase("memory-copy")]
    [TestCase("unknown-shift")]
    [TestCase("narrow-shift")]
    [TestCase("signed-shift")]
    [TestCase("other-count")]
    [TestCase("variable-count")]
    [TestCase("unknown-conversion")]
    [TestCase("signed-conversion")]
    [TestCase("phi")]
    [TestCase("duplicate-definition")]
    [TestCase("non-dominating-copy")]
    [TestCase("cycle")]
    public void UnprovenBitViewsAreRejectedWithoutMutation(string shape)
    {
        var f = Fixture(true);
        switch (shape)
        {
            case "unknown-copy": f.Steps[1].NativeRegisterCopySize = 0; break;
            case "narrow-copy": f.Steps[1].NativeRegisterCopySize = 4; break;
            case "memory-copy": f.Steps[1].NativeReadSize = 8; break;
            case "unknown-shift": f.Steps[3].NativeArithmeticSize = 0; break;
            case "narrow-shift": f.Steps[3].NativeArithmeticSize = 4; break;
            case "signed-shift": f.Steps[3].OpCode = OpCode.ShiftRight; break;
            case "other-count": f.Steps[3].SetOperand(2, new Immediate(16)); break;
            case "variable-count": f.Steps[3].SetOperand(2, f.Value); break;
            case "unknown-conversion": f.Steps[2].NativeArithmeticSize = 0; break;
            case "signed-conversion": f.Steps[2].SetOperand(2, TestGameLoader.LoadSimple2019Game().SystemTypes.SystemInt64Type); break;
            case "phi": f.Steps[1].OpCode = OpCode.Phi; break;
            case "duplicate-definition":
                f.Steps.Insert(2, new(-1, OpCode.Move, f.Steps[1].Destination!, f.Root) { NativeRegisterCopySize = 8 }); break;
            case "non-dominating-copy":
                var copy = f.Steps[1]; f.Steps.RemoveAt(1); f.Steps.Add(copy); break;
            case "cycle": f.Steps[1].SetOperand(1, f.Value); break;
        }
        var originalOperands = f.Steps.Select(i => i.Operands.ToArray()).ToArray();
        Assert.That(Arm64AggregateReturnLowWordRecovery.TryResolveRegisterView(f.Graph, Definitions(f.Graph), f.Compare,
            f.Value, out _, out _, out _), Is.False, shape);
        for (var i = 0; i < f.Steps.Count; i++) Assert.That(f.Steps[i].Operands.ToArray(), Is.EqualTo(originalOperands[i]));
    }
}
