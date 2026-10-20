using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Tests.Analysis;

public class IndirectMetadataRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("valid-other-block",true)]
    [TestCase("different-slot",false)]
    [TestCase("partial-definition",false)]
    [TestCase("unknown-definition",false)]
    [TestCase("mutable-slot",false)]
    [TestCase("partial-use",false)]
    [TestCase("offset-use",false)]
    [TestCase("indexed-use",false)]
    [TestCase("before-definition",false)]
    [TestCase("implicit-clobber",false)]
    [TestCase("non-dominating-branch",false)]
    public void RepeatedSlotsNeedExactWidthsAndADominatingDefinition(string shape,bool expected)
    {
        var pointer=new LocalVariable("pointer",new(null,"X22"));
        var result=new LocalVariable("result",new(null,"X0"));
        var one=new Instruction(0,OpCode.Move,pointer,new MemoryOperand(addend:0x1000)){NativeReadSize=8};
        var two=new Instruction(1,OpCode.Move,pointer,new MemoryOperand(addend:shape=="different-slot"?0x1100:0x1000)){NativeReadSize=8};
        var use=new Instruction(2,OpCode.Move,result,new MemoryOperand(pointer)){NativeReadSize=8};
        if(shape=="partial-definition")two.NativeReadSize=4;
        if(shape=="unknown-definition")two.SetOperand(1,new Immediate(0x1000));
        if(shape=="partial-use")use.NativeReadSize=4;
        if(shape=="offset-use")use.SetOperand(1,new MemoryOperand(pointer,addend:8));
        if(shape=="indexed-use")use.SetOperand(1,new MemoryOperand(pointer,pointer,scale:8));
        var instructions=new List<Instruction>{one,use,two,new(3,OpCode.Return)};
        if(shape=="valid-other-block")instructions=[one,new(5,OpCode.Jump,use),use,two,instructions[^1]];
        if(shape=="before-definition")instructions=[use,one,two,instructions[^1]];
        if(shape=="implicit-clobber")instructions.Insert(1,new(4,OpCode.CallVoid,new StringLiteral("callback")){ImplicitDefinition=pointer.Register});
        if(shape=="non-dominating-branch")
        {
            var bypass=new Instruction(5,OpCode.Nop);
            instructions=[new(6,OpCode.ConditionalJump,bypass,new LocalVariable("condition",new(null,"flag"))),
                one,two,new(7,OpCode.Jump,use),bypass,new(8,OpCode.Jump,use),use,new(9,OpCode.Return)];
        }
        var graph=new ISILControlFlowGraph(instructions);
        var definitions=graph.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).ToDictionary(g=>g.Key,g=>g.ToArray());
        DominatorInfo? dominance=null;
        var before=graph.Instructions.ToArray();
        var address=MetadataResolver.RepeatedGotMetadataAddress(use,graph,definitions,8,
            slot=>slot==0x1000 && shape!="mutable-slot"?0x2000UL:null,ref dominance);
        Assert.That(address,Is.EqualTo(expected?0x2000UL:(ulong?)null));
        Assert.That(graph.Instructions,Is.EqualTo(before),"metadata address proof must not edit control flow");
    }

    [Test]
    public void DoubleLoad_ResolvesOnlySecondDereference()
    {
        var pointer = new LocalVariable("pointer", new Register(null, "x8"));
        var slot = new MemoryOperand(addend: 0x1000);
        var definitions = new Dictionary<LocalVariable, Instruction> { [pointer] = new(0, OpCode.Move, pointer, slot) };
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), definitions,
            address => address == 0x1000 ? 0x2000UL : null), Is.EqualTo(0x2000UL));
        Assert.That(MetadataResolver.IndirectMetadataAddress(slot, definitions, _ => 0x2000UL), Is.Null);
    }

    [Test]
    public void MutableGlobalAndNonzeroOffsets_AreNotCollapsed()
    {
        var pointer = new LocalVariable("pointer", new Register(null, "x8"));
        var definitions = new Dictionary<LocalVariable, Instruction> { [pointer] = new(0, OpCode.Move, pointer, new MemoryOperand(addend: 0x1000)) };
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), definitions, _ => null), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer, addend: 8), definitions, _ => 0x2000UL), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer, pointer, scale: 8), definitions, _ => 0x2000UL), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), new Dictionary<LocalVariable, Instruction>(), _ => 0x2000UL), Is.Null);
    }
}
