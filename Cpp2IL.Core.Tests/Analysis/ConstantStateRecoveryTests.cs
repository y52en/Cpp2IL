using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstantStateRecoveryTests
{
    static LocalVariable Local(string name) => new(name,new(null,name));

    [TestCase("same",true)]
    [TestCase("direct",true)]
    [TestCase("anchored-loop",true)]
    [TestCase("different",false)]
    [TestCase("unknown",false)]
    [TestCase("unanchored-loop",false)]
    [TestCase("missing-edge",false)]
    [TestCase("addressed",false)]
    [TestCase("parameter",false)]
    [TestCase("multiply-defined",false)]
    [TestCase("different-width-representation",false)]
    [TestCase("floating-payload",false)]
    public void PhiConstantNeedsEveryIncomingValueAndAnImmutableAnchoredResult(string shape,bool expected)
    {
        var a=Local("a");var b=Local("b");var value=Local("state");var condition=Local("condition");
        var cfg=new ISILControlFlowGraph([]);
        var branch=new Block{ID=10};var left=new Block{ID=11};var right=new Block{ID=12};var join=new Block{ID=13};
        cfg.Blocks=[cfg.EntryBlock,cfg.ExitBlock,branch,left,right,join];
        foreach(var block in cfg.Blocks){block.Successors.Clear();block.Predecessors.Clear();}
        void Edge(Block from,Block to){from.Successors.Add(to);to.Predecessors.Add(from);}
        Edge(cfg.EntryBlock,branch);Edge(branch,left);Edge(branch,right);Edge(left,join);Edge(right,join);Edge(join,cfg.ExitBlock);
        branch.Instructions=[new(0,OpCode.ConditionalJump,left,condition)];
        left.Instructions=[new(1,OpCode.Move,a,new Immediate(0)),new(2,OpCode.Jump,join)];
        right.Instructions=[new(3,OpCode.Move,b,new Immediate(shape=="different"?1:0)),new(4,OpCode.Jump,join)];
        var phi=new Instruction(5,OpCode.Phi,value,a,b);var read=new Instruction(6,OpCode.Return,value);
        join.Instructions=[phi,read];var parameters=new List<LocalVariable>{condition};
        if(shape=="direct")phi.SetOperands(value,new Immediate(0),new Immediate(0));
        if(shape=="unknown"){right.Instructions.RemoveAt(0);parameters.Add(b);}
        if(shape=="anchored-loop" || shape=="unanchored-loop")
        {
            right.Instructions.Clear();right.Successors.Clear();join.Predecessors.Remove(right);
            Edge(join,join);phi.SetOperands(value,shape=="anchored-loop"?a:value,value);
        }
        if(shape=="missing-edge")phi.RemoveOperandAt(2);
        if(shape=="addressed")join.Instructions.Insert(1,new(7,OpCode.CallVoid,new Immediate(1234),new AddressOf(value)));
        if(shape=="parameter")parameters.Add(value);
        if(shape=="multiply-defined")left.Instructions.Insert(0,new(7,OpCode.Move,value,new Immediate(1)));
        if(shape=="different-width-representation")phi.SetOperands(value,new Immediate(-1),new Immediate(uint.MaxValue));
        if(shape=="floating-payload")value.Type=TestGameLoader.LoadSimple2019Game().SystemTypes.SystemSingleType;
        SsaSimplifier.Run(cfg,parameters);
        if(expected){Assert.That(read.Operands[0],Is.TypeOf<Immediate>());Assert.That(((Immediate)read.Operands[0]).Value,Is.Zero);}
        else Assert.That(read.Operands[0],Is.SameAs(value));
    }

    [TestCase(0L,-1L,0L)]
    [TestCase(-1L,-1L,1L)]
    [TestCase(0L,0L,1L)]
    [TestCase(long.MinValue,long.MinValue,1L)]
    [TestCase(long.MinValue,long.MaxValue,0L)]
    public void ZeroDifferenceConstantAgreesAtEveryIntegerWidth(long a,long b,long expected)
    {
        foreach(var inverted in new[]{false,true})
        {
            var difference=Local("difference");var flag=Local("flag");
            var subtraction=new Instruction(0,OpCode.Subtract,difference,new Immediate(a),new Immediate(b));
            var check=new Instruction(1,inverted?OpCode.CheckNotEqual:OpCode.CheckEqual,flag,difference,new Immediate(0));
            var cfg=new ISILControlFlowGraph([subtraction,check,new(2,OpCode.Return,flag)]);
            Assert.That(ConstantFolder.Run(cfg),Is.True);
            Assert.That(check.OpCode,Is.EqualTo(OpCode.Move));
            Assert.That(((Immediate)check.Operands[1]).Value,Is.EqualTo(inverted?1-expected:expected));
            if(b!=0)Assert.That(subtraction.OpCode,Is.EqualTo(OpCode.Subtract),"other flags/consumers retain the original subtraction");
        }
    }

    [TestCase(256L,0L)]
    [TestCase(65536L,0L)]
    [TestCase(4294967296L,0L)]
    [TestCase(-1L,4294967295L)]
    public void UnknownWidthNeverMakesTruncatingEqualitiesEquivalent(long a,long b)
    {
        var difference=Local("difference");var flag=Local("flag");
        var check=new Instruction(1,OpCode.CheckEqual,flag,difference,new Immediate(0));
        var cfg=new ISILControlFlowGraph([new(0,OpCode.Subtract,difference,new Immediate(a),new Immediate(b)),check,new(2,OpCode.Return,flag)]);
        ConstantFolder.Run(cfg);Assert.That(check.OpCode,Is.EqualTo(OpCode.CheckEqual));
    }
}
