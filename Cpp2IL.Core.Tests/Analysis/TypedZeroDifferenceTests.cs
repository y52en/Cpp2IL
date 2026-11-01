using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypedZeroDifferenceTests
{
    [TestCase("Boolean",true)] [TestCase("Byte",true)] [TestCase("SByte",true)]
    [TestCase("Char",true)] [TestCase("Int16",true)] [TestCase("UInt16",true)]
    [TestCase("Int32",true)] [TestCase("UInt32",true)]
    [TestCase("Int64",false)] [TestCase("UInt64",false)]
    [TestCase("Object",false)] [TestCase("Single",false)]
    [TestCase("unknown",false)] [TestCase("wide-native",false)]
    [TestCase("changed-snapshot",false)] [TestCase("addressed",false)]
    [TestCase("enum",true)] [TestCase("separate-block",false)] [TestCase("unknown-width",false)]
    public void WordDifferenceZeroNeedsAnUnchangedKnownI4Source(string shape,bool expected)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        foreach(var inverted in new[]{false,true})
        {
            var name=shape=="enum"?"AttributeTargets":shape.Contains('-') || shape=="addressed"?"Int32":shape;
            var type=shape=="unknown"?null:types.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System."+name);
            if(shape!="unknown")Assert.That(type,Is.Not.Null);
            var source=new LocalVariable("source",new(null,"source"),type);
            var difference=new LocalVariable("difference",new(null,"difference"));
            var flag=new LocalVariable("flag",new(null,"flag"),types.SystemBooleanType);
            var subtract=new Instruction(0,OpCode.Subtract,difference,source,new Immediate(0))
                {NativeArithmeticSize=shape=="wide-native"?8:shape=="unknown-width"?0:4};
            var check=new Instruction(2,inverted?OpCode.CheckNotEqual:OpCode.CheckEqual,flag,difference,new Immediate(0));
            var graph=new ISILControlFlowGraph([subtract,check,new(3,OpCode.Return,flag)]);
            var block=graph.Blocks.Single(b=>b.Instructions.Contains(check));
            if(shape=="changed-snapshot")block.Instructions.Insert(1,new(1,OpCode.Move,source,new Immediate(1)));
            if(shape=="addressed")block.Instructions.Insert(1,new(1,OpCode.CallVoid,new Immediate(123),new AddressOf(source)));
            if(shape=="separate-block")
            {
                var next=new Block{ID=99,Instructions=block.Instructions.Skip(1).ToList()};
                block.Instructions.RemoveRange(1,block.Instructions.Count-1);
                block.Successors.Clear();block.Successors.Add(next);next.Predecessors.Add(block);
                next.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Remove(block);
                graph.ExitBlock.Predecessors.Add(next);graph.Blocks.Add(next);
            }
            ConstantFolder.Run(graph);
            Assert.That(ReferenceEquals(check.Operands[1],source),Is.EqualTo(expected));
            if(expected)
            {
                Assert.That(check.OpCode,Is.EqualTo(inverted?OpCode.CheckNotEqual:OpCode.CheckEqual));
                Assert.That(((Immediate)check.Operands[2]).Value,Is.Zero);
                DeadCodeEliminator.Run(graph);Assert.That(subtract.OpCode,Is.EqualTo(OpCode.Nop));
            }
        }
    }
}
