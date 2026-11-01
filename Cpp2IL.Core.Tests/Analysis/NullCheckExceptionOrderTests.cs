using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NullCheckExceptionOrderTests
{
    [TestCase("call")]
    [TestCase("unbox")]
    [TestCase("write")]
    [TestCase("divide")]
    [TestCase("return")]
    [TestCase("different-array")]
    [TestCase("unknown-type")]
    [TestCase("redefined-receiver")]
    public void MustNotDelayNullThrowPastOtherEffectsOrExceptions(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var arrayType=new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type);
        var receiver=new LocalVariable("array",new Register(null,"array"),shape=="unknown-type"?null:arrayType);
        var other=new LocalVariable("other",new Register(null,"other"),arrayType);
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var number=new LocalVariable("number",new Register(null,"number"),app.SystemTypes.SystemInt32Type);
        var condition=new LocalVariable("condition",new Register(null,"condition"),app.SystemTypes.SystemBooleanType);
        var exception=app.SystemTypes.SystemExceptionType.DeclaringAssembly.GetTypeByFullName("System.NullReferenceException")!;
        var check=new Instruction(0,OpCode.CheckEqual,condition,receiver,new Immediate(0));
        var throwing=new Instruction(20,OpCode.Throw,exception);
        var jump=new Instruction(1,OpCode.ConditionalJump,throwing,condition);
        Instruction first=shape switch {
            "call"=>new(2,OpCode.CallVoid,new Immediate(0x1234),value),
            "unbox"=>new(2,OpCode.UnboxAny,number,app.SystemTypes.SystemInt32Type,value),
            "write"=>new(2,OpCode.Move,new MemoryOperand(value,addend:16),new Immediate(1)),
            "divide"=>new(2,OpCode.Divide,number,new Immediate(1),new Immediate(0)),
            "return"=>new(2,OpCode.Return,receiver),
            "different-array"=>new(2,OpCode.Move,number,new ArrayLength(other)),
            "redefined-receiver"=>new(2,OpCode.Move,receiver,other),
            _=>new(2,OpCode.Move,number,new ArrayLength(receiver))};
        var instructions=new List<Instruction>{check,jump,first,new(3,OpCode.Move,number,new ArrayLength(receiver)),
            new(4,OpCode.Return),throwing,new(21,OpCode.Return)};
        var graph=new ISILControlFlowGraph(instructions);
        InjectedCheckRemover.Run(graph);
        if(shape=="unknown-type")
        {
            Assert.That(jump.OpCode,Is.EqualTo(OpCode.ConditionalJump));
            Assert.That(graph.Instructions.Contains(throwing),Is.True);
            Assert.That(graph.Instructions.Any(i=>i.OpCode==OpCode.ArrayNullCheck),Is.False);
        }
        else
        {
            Assert.That(jump.OpCode,Is.EqualTo(OpCode.Jump));
            var guard=graph.Instructions.Single(i=>i.OpCode==OpCode.ArrayNullCheck);
            Assert.That(guard.Operands[0],Is.SameAs(receiver));
            Assert.That(guard.Destination,Is.Null);
            Assert.That(guard.Sources,Is.EquivalentTo(new[]{receiver}));
            Assert.That(ForwardNullCheckRecovery.DefinitionDominates(graph,guard,first),Is.True);
        }
    }
}
