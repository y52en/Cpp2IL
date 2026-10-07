using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InjectedCheckRemoverTests
{
    private static Immediate Imm(long value) => new() { Value=value };

    [TestCase(true,false)]
    [TestCase(true,true)]
    [TestCase(false,false)]
    [TestCase(false,true)]
    public void RemovesOnlyNullEdgeForBothBranchDirections(bool targetThrows,bool reversedOperands)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var exception=app.SystemTypes.SystemExceptionType.DeclaringAssembly.GetTypeByFullName("System.NullReferenceException")!;
        Assert.That(exception,Is.Not.Null);
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var cond=new LocalVariable("cond",new Register(null,"cond"),app.SystemTypes.SystemBooleanType);
        var check=new Instruction(0,targetThrows?OpCode.CheckEqual:OpCode.CheckNotEqual,cond,
            reversedOperands?Imm(0):value,reversedOperands?value:Imm(0));
        var throwing=new Instruction(targetThrows?4:2,OpCode.Throw,exception);
        var success=new Instruction(targetThrows?2:4,OpCode.Return,value);
        var jump=new Instruction(1,OpCode.ConditionalJump,targetThrows?throwing:success,cond);
        var graph=new ISILControlFlowGraph(targetThrows
            ? [check,jump,success,new(3,OpCode.Return),throwing,new(5,OpCode.Return)]
            : [check,jump,throwing,new(3,OpCode.Return),success]);
        InjectedCheckRemover.Run(graph);
        Assert.That(jump.OpCode,Is.EqualTo(OpCode.Jump));
        Assert.That(graph.Instructions.Contains(throwing),Is.False);
        Assert.That(graph.Instructions.Contains(success),Is.True);
        var source=graph.Blocks.Single(b=>b.Instructions.Contains(jump));
        Assert.That(source.Successors.Count,Is.EqualTo(1));
        Assert.That(jump.Operands[0],Is.SameAs(source.Successors[0]));
    }

    [TestCase("wrong-polarity")]
    [TestCase("side-effect")]
    [TestCase("explicit-object-throw")]
    [TestCase("nonzero-comparison")]
    public void UnknownOrSourceVisibleThrowIsPreserved(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var exception=app.SystemTypes.SystemExceptionType.DeclaringAssembly.GetTypeByFullName("System.NullReferenceException")!;
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var cond=new LocalVariable("cond",new Register(null,"cond"));
        var check=new Instruction(0,shape=="wrong-polarity"?OpCode.CheckEqual:OpCode.CheckNotEqual,cond,value,Imm(shape=="nonzero-comparison"?1:0));
        var throwing=new Instruction(3,OpCode.Throw,shape=="explicit-object-throw"?value:exception);
        var success=new Instruction(5,OpCode.Return,value);
        var jump=new Instruction(1,OpCode.ConditionalJump,success,cond);
        var list=new List<Instruction>{check,jump};
        if(shape=="side-effect")list.Add(new(2,OpCode.Move,new MemoryOperand(value,null,16,0),Imm(1)));
        list.AddRange([throwing,new(4,OpCode.Return),success]);
        var graph=new ISILControlFlowGraph(list);
        InjectedCheckRemover.Run(graph);
        Assert.That(jump.OpCode,Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(graph.Instructions.Contains(throwing),Is.True);
    }
}
