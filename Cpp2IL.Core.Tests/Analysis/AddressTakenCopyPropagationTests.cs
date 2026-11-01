using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class AddressTakenCopyPropagationTests
{
    private static LocalVariable Local(string name) => new(name, new Register(null, name));
    private static MethodAnalysisContext Method(ISILControlFlowGraph graph, params LocalVariable[] locals)
    {
        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = graph; method.Locals = locals.ToList(); method.ParameterLocals = [];
        return method;
    }

    [Test]
    public void OutArgumentIsAReachingDefinitionAtBranchJoin()
    {
        var slot = Local("stack_-48"); var created = Local("created"); var condition = Local("condition");
        var ret = new Instruction(5, OpCode.Return, slot);
        var assign = new Instruction(3, OpCode.Move, slot, created);
        var jump = new Instruction(2, OpCode.Jump, ret);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CallVoid, new StringLiteral("TryGetValue"), new AddressOf(slot)),
            new(1, OpCode.ConditionalJump, assign, condition), jump,
            assign, new(4, OpCode.Jump, ret), ret
        };
        var graph = new ISILControlFlowGraph(instructions);
        Simplifier.Simplify(Method(graph, slot, created, condition));
        Assert.That(ret.Operands[0], Is.SameAs(slot), "the other branch obtains its value through the out call");
        Assert.That(graph.Instructions.Any(i => ReferenceEquals(i.Destination, slot)), Is.True);
    }

    [Test]
    public void TakingDestinationAddressStopsForwardingAnEarlierCopy()
    {
        var slot = Local("stack_-48"); var original = Local("original");
        var assign = new Instruction(0, OpCode.Move, slot, original);
        var ret = new Instruction(2, OpCode.Return, slot);
        var graph = new ISILControlFlowGraph([assign,
            new(1, OpCode.CallVoid, new StringLiteral("Mutate"), new AddressOf(slot)), ret]);
        Simplifier.Simplify(Method(graph, slot, original));
        Assert.That(ret.Operands[0], Is.SameAs(slot));
        Assert.That(assign.OpCode, Is.EqualTo(OpCode.Move));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void SnapshotCannotBeReplacedBySourceModifiedAfterCopy(bool addressWrite)
    {
        var source = Local("source"); var snapshot = Local("snapshot"); var replacement = Local("replacement");
        var assign = new Instruction(0, OpCode.Move, snapshot, source);
        var ret = new Instruction(2, OpCode.Return, snapshot);
        var mutation = addressWrite
            ? new Instruction(1, OpCode.CallVoid, new StringLiteral("Mutate"), new AddressOf(source))
            : new Instruction(1, OpCode.Move, source, replacement);
        var graph = new ISILControlFlowGraph([assign, mutation, ret]);
        Simplifier.Simplify(Method(graph, source, snapshot, replacement));
        Assert.That(ret.Operands[0], Is.Not.SameAs(replacement));
        if (addressWrite)
        {
            Assert.That(ret.Operands[0], Is.SameAs(snapshot));
            Assert.That(assign.OpCode, Is.EqualTo(OpCode.Move));
        }
        else
        {
            // Dropping the now-dead overwrite also makes returning the unchanged
            // original source legal; demand the old VALUE, not a particular name.
            Assert.That(ReferenceEquals(ret.Operands[0], snapshot)
                || ReferenceEquals(ret.Operands[0], source) && mutation.OpCode == OpCode.Nop, Is.True);
        }
    }
}
