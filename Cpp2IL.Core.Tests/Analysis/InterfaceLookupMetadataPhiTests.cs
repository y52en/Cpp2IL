using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceLookupMetadataPhiTests
{
    [TestCase("valid", true)]
    [TestCase("nested", true)]
    [TestCase("unmatched", false)]
    [TestCase("unrelated-merge", false)]
    [TestCase("nonzero", false)]
    [TestCase("unknown", false)]
    [TestCase("name-only", false)]
    [TestCase("cycle", false)]
    [TestCase("memory", false)]
    [TestCase("no-zero", false)]
    [TestCase("no-incoming", false)]
    public void OnlyZeroAndIncomingMetadataFromThisLookupMergeQualify(string shape, bool expected)
    {
        LocalVariable Local(string n) => new(n, new(null, n));
        var incoming = Local("methodInfo"); incoming.IsMethodInfo = shape != "name-only";
        var lookup = Local("lookup"); var merged = Local("merged"); var outer = Local("outer");
        var matched = new Instruction(-1, OpCode.Phi, lookup, new Immediate(0), new Immediate(1));
        IOperand zero = shape switch { "nonzero" => new Immediate(1), "unknown" => Local("unknown"),
            "memory" => new MemoryOperand(incoming), "no-zero" => incoming, _ => new Immediate(0) };
        var phi = new Instruction(-1, OpCode.Phi, merged, shape == "no-incoming" ? new Immediate(0) : incoming, zero);
        var home = new Block { ID = 20 };
        var definitions = new Dictionary<LocalVariable, Instruction> { [lookup] = matched, [merged] = phi };
        var homes = new Dictionary<Instruction, Block> { [matched] = home, [phi] = shape == "unrelated-merge" ? new Block { ID = 21 } : home };
        IOperand value = merged;
        if (shape == "nested")
        {
            var nested = new Instruction(-1, OpCode.Phi, outer, merged, incoming, incoming);
            definitions[outer] = nested; homes[nested] = new Block { ID = 22 }; value = outer;
        }
        if (shape == "cycle") phi.SetOperand(2, merged);
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(value, definitions, homes,
            shape == "unmatched" ? [] : [matched]), Is.EqualTo(expected));
    }
}
