using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceLookupMetadataPhiTests
{
    [TestCase("valid", true)]
    [TestCase("foreign-lookup", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("partial-read", false)]
    [TestCase("not-approved-incoming", false)]
    [TestCase("no-matched-load", false)]
    [TestCase("effectful-incoming", false)]
    [TestCase("known-defined-metadata", true)]
    [TestCase("unknown-defined-metadata", false)]
    [TestCase("cycle", false)]
    public void IgnoredRawIncomingRequiresActualMatchedMetadataLoad(string shape, bool expected)
    {
        LocalVariable Local(string n) => new(n, new(null, n));
        var incoming=Local("raw-entry-register"); var lookup=Local("lookup");
        var foreign=Local("foreign"); var loaded=Local("loaded"); var merged=Local("merged");
        var matched=new Instruction(-1,OpCode.Phi,lookup,new Immediate(0),new Immediate(1));
        var read=new Instruction(2,OpCode.Move,loaded,new MemoryOperand(
            shape=="foreign-lookup" ? foreign : lookup,addend:shape=="wrong-offset" ? 0 : 8))
            {NativeReadSize=shape=="partial-read" ? 4 : 8};
        var phi=new Instruction(-1,OpCode.Phi,merged,
            shape=="no-matched-load" ? new Immediate(0) : loaded,incoming);
        var definitions=new Dictionary<LocalVariable,Instruction>
            {[lookup]=matched,[loaded]=read,[merged]=phi};
        var homes=new Dictionary<Instruction,Block>
            {[matched]=new(){ID=20},[phi]=new(){ID=21}};
        if(shape=="effectful-incoming")
            definitions[incoming]=new(3,OpCode.Move,incoming,new MemoryOperand(foreign));
        if(shape is "known-defined-metadata" or "unknown-defined-metadata")
            definitions[incoming]=new(3,OpCode.Move,incoming,new MemoryOperand(foreign));
        if(shape=="cycle")phi.SetOperand(2,merged);
        // The default metadata-only recognizer must continue rejecting raw
        // registers, even when the stronger hidden-operand proof can opt in.
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(
            merged,definitions,homes,[matched]),Is.False);
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(
            merged,definitions,homes,[matched],
            local=>ReferenceEquals(local,incoming)&&shape!="not-approved-incoming",
            local=>ReferenceEquals(local,incoming)&&shape=="known-defined-metadata"),Is.EqualTo(expected));
    }

    [Test]
    public void RawIncomingCannotPiggybackOnTheOlderZeroMetadataRoute()
    {
        LocalVariable Local(string n) => new(n,new(null,n));
        var metadata=Local("metadata"); metadata.IsMethodInfo=true;
        var raw=Local("raw"); var lookup=Local("lookup"); var merged=Local("merged");
        var matched=new Instruction(-1,OpCode.Phi,lookup,new Immediate(0),new Immediate(1));
        var phi=new Instruction(-1,OpCode.Phi,merged,metadata,new Immediate(0),raw);
        var block=new Block(){ID=20};
        var definitions=new Dictionary<LocalVariable,Instruction>{[lookup]=matched,[merged]=phi};
        var homes=new Dictionary<Instruction,Block>{[matched]=block,[phi]=block};
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(
            merged,definitions,homes,[matched],local=>ReferenceEquals(local,raw)),Is.False);
    }

    [TestCase("valid", true)]
    [TestCase("nested-copy", true)]
    [TestCase("foreign-lookup", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("partial-read", false)]
    [TestCase("unknown-alternative", false)]
    [TestCase("nonzero-alternative", false)]
    [TestCase("incoming-name-only", false)]
    [TestCase("no-incoming", false)]
    [TestCase("cycle", false)]
    public void MatchedInvokeDataInfoMayJoinIncomingMetadataOutsideTheLookupMerge(string shape, bool expected)
    {
        LocalVariable Local(string n) => new(n, new(null, n));
        var incoming = Local("methodInfo"); incoming.IsMethodInfo = shape != "incoming-name-only";
        var lookup = Local("lookup"); var foreign = Local("foreign"); var loaded = Local("loaded");
        var merged = Local("merged"); var copied = Local("copied");
        var matched = new Instruction(-1, OpCode.Phi, lookup, new Immediate(0), new Immediate(1));
        var foreignPhi = new Instruction(-1, OpCode.Phi, foreign, new Immediate(0), new Immediate(1));
        var read = new Instruction(2, OpCode.Move, loaded,
            new MemoryOperand(shape == "foreign-lookup" ? foreign : lookup, addend: shape == "wrong-offset" ? 0 : 8))
            { NativeReadSize = shape == "partial-read" ? 4 : 8 };
        IOperand alternate = shape switch { "unknown-alternative" => Local("unknown"),
            "nonzero-alternative" => new Immediate(7), "no-incoming" => new Immediate(0), _ => incoming };
        var phi = new Instruction(-1, OpCode.Phi, merged, loaded, alternate);
        var definitions = new Dictionary<LocalVariable, Instruction>
            { [lookup] = matched, [foreign] = foreignPhi, [loaded] = read, [merged] = phi };
        var homes = new Dictionary<Instruction, Block>
            { [matched] = new() { ID = 20 }, [foreignPhi] = new() { ID = 21 }, [phi] = new() { ID = 22 } };
        IOperand value = merged;
        if (shape == "nested-copy")
        {
            definitions[copied] = new(3, OpCode.Move, copied, merged); value = copied;
        }
        if (shape == "cycle") phi.SetOperand(2, merged);
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(value, definitions, homes, [matched]), Is.EqualTo(expected));
    }

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
