using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class BoxAddressRecoveryTests
{
    private static Immediate Imm(ulong value) => new() { Value = unchecked((long)value) };

    [Test]
    public void StoreAfterAddressReachesBoxInSsa()
    {
        var slot = new Register(null,"stack_-28");
        var pointer = new Register(null,"x1");
        var result = new Register(null,"x0");
        var address = new Instruction(0,OpCode.Move,pointer,new AddressOf(slot));
        var store = new Instruction(1,OpCode.Move,slot,Imm(42));
        var box = new Instruction(2,OpCode.Call,Imm(0x1234),result,Imm(0x5678),pointer);
        var graph = new ISILControlFlowGraph([address,store,box,new(3,OpCode.Return,result)]);
        Assert.That(BoxAddressRecovery.Run(graph,new HashSet<ulong>{0x1234}),Is.EqualTo(1));
        SsaForm.Build(graph,new DominatorInfo(graph));
        var target = (Register)((AddressOf)address.Operands[1]).Target;
        Assert.That(target,Is.EqualTo((Register)store.Destination!));
        Assert.That(target.Version,Is.EqualTo(-1),"an addressed physical stack slot remains stable mutable storage");
    }

    [TestCase("unknown-call")]
    [TestCase("earlier-use")]
    [TestCase("earlier-memory-use")]
    [TestCase("pointer-redefined")]
    [TestCase("intervening-call")]
    [TestCase("not-stack")]
    [TestCase("no-store")]
    public void UnprovenShapesAreUnchanged(string shape)
    {
        var slot = new Register(null,shape=="not-stack"?"ordinary":"stack_-18");
        var pointer = new Register(null,"x1");
        var result = new Register(null,"x0");
        var address = new Instruction(0,OpCode.Move,pointer,new AddressOf(slot));
        var list = new List<Instruction>{address};
        if (shape=="earlier-use") list.Add(new(1,OpCode.Move,new Register(null,"copy"),pointer));
        if (shape=="earlier-memory-use") list.Add(new(1,OpCode.Move,new Register(null,"copy"),new MemoryOperand(pointer,null,0,0)));
        if (shape=="pointer-redefined") list.Add(new(1,OpCode.Move,pointer,Imm(0)));
        if (shape=="intervening-call") list.Add(new(1,OpCode.Call,Imm(0x9999),result));
        if (shape!="no-store") list.Add(new(2,OpCode.Move,slot,Imm(42)));
        list.Add(new(3,OpCode.Call,Imm(shape=="unknown-call"?0x9999ul:0x1234ul),result,Imm(0x5678),pointer));
        list.Add(new(4,OpCode.Return,result));
        var graph = new ISILControlFlowGraph(list);
        var before = graph.Instructions.ToArray();
        Assert.That(BoxAddressRecovery.Run(graph,new HashSet<ulong>{0x1234}),Is.Zero);
        Assert.That(graph.Instructions.ToArray(),Is.EqualTo(before));
    }
}
