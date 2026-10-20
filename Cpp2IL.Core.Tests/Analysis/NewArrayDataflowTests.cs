using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class NewArrayDataflowTests
{
    [Test]
    public void AllocationDefinesItsResultAndDestinationSetterRetargetsIt()
    {
        var array=new LocalVariable("array",new(null,"X0"));
        var replacement=new LocalVariable("replacement",new(null,"X1"));
        var length=new LocalVariable("length",new(null,"X2"));
        var allocation=new Instruction(0,OpCode.NewArr,array,new StringLiteral("metadata-type"),length);
        Assert.That(allocation.Destination,Is.SameAs(array));
        Assert.That(allocation.IsAssignment,Is.True);
        allocation.Destination=replacement;
        Assert.That(allocation.Operands[0],Is.SameAs(replacement));
        Assert.That(allocation.Destination,Is.SameAs(replacement));
    }

    [Test]
    public void RuntimeTypeAndLengthAreInputsButTheDestinationIsNot()
    {
        var array=new LocalVariable("array",new(null,"X0"));
        var type=new LocalVariable("type",new(null,"X1"));
        var length=new LocalVariable("length",new(null,"X2"));
        var allocation=new Instruction(0,OpCode.NewArr,array,type,length);
        Assert.That(allocation.Sources.ToArray(),Is.EquivalentTo(new IOperand[]{type,length}));
        Assert.That(allocation.SourcesAndConstants.ToArray(),Is.EquivalentTo(new IOperand[]{type,length}));
        allocation.SetOperand(2,new Immediate(7));
        Assert.That(allocation.Sources.ToArray(),Is.EqualTo(new IOperand[]{type}));
        Assert.That(allocation.SourcesAndConstants.ToArray().OfType<Immediate>().Single().Value,Is.EqualTo(7));
    }

    [Test]
    public void DceMustKeepTheLengthProducerForAReturnedArray()
    {
        var array=new LocalVariable("array",new(null,"X0"));
        var length=new LocalVariable("length",new(null,"X1"));
        var calculate=new Instruction(0,OpCode.Add,length,new Immediate(2),new Immediate(3));
        var allocation=new Instruction(1,OpCode.NewArr,array,new StringLiteral("metadata-type"),length);
        var graph=new ISILControlFlowGraph([calculate,allocation,new(2,OpCode.Return,array)]);
        DeadCodeEliminator.Run(graph);
        Assert.That(graph.Instructions.Contains(calculate),Is.True,
            "length is an allocation input, not dead arithmetic");
        Assert.That(graph.Instructions.Contains(allocation),Is.True);
    }
}
