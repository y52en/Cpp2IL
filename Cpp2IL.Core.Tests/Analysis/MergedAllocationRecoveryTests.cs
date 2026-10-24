using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MergedAllocationRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("unknown-edge",false)]
    [TestCase("duplicate-definition",false)]
    [TestCase("effect-between-allocation-and-constructor",false)]
    [TestCase("callback-suffix",false)]
    [TestCase("ambiguous-template",false)]
    [TestCase("wrong-constructor",false)]
    [TestCase("wrong-parameters",false)]
    [TestCase("late-argument",false)]
    [TestCase("virtual",false)]
    [TestCase("cycle",false)]
    [TestCase("conditional-edge",false)]
    [TestCase("instruction-target",false)]
    [TestCase("same-type",false)]
    [TestCase("phi",false)]
    public void SpecializesOnlyAllProvenAllocationEdges(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;var assembly=t.SystemObjectType.DeclaringAssembly;
        var parent=new InjectedTypeAnalysisContext(assembly,"Test","Parent",t.SystemObjectType,TypeAttributes.Public);
        var a=new InjectedTypeAnalysisContext(assembly,"Test","A",parent,TypeAttributes.Public);
        var b=shape=="same-type"?a:new InjectedTypeAnalysisContext(assembly,"Test","B",parent,TypeAttributes.Public);
        var baseCtor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType);
        var ctorA=a.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType);
        var ctorB=b.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,
            shape=="wrong-parameters"?t.SystemInt32Type:t.SystemStringType);
        var templateA=new ForwardedConstructorRecovery.Template(ctorA,baseCtor);
        var templateB=new ForwardedConstructorRecovery.Template(ctorB,shape=="wrong-constructor"?ctorA:baseCtor);
        a.PutExtraData(ForwardedConstructorRecovery.CacheKey,new[]{templateA});
        b.PutExtraData(ForwardedConstructorRecovery.CacheKey,shape=="ambiguous-template"?new[]{templateB,templateB}:new[]{templateB});
        LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new Register(null,name),type);
        var method=new InjectedMethodAnalysisContext(parent,"Make",parent,MethodAttributes.Public|MethodAttributes.Static,[t.SystemStringType]);
        var argument=Local("arg",t.SystemStringType);method.ParameterLocals=[argument];
        var obj=Local("obj",parent);var metadata=Local("metadata");var result=Local("result",parent);
        method.Locals=[obj,metadata,result,argument];
        var graph=new ISILControlFlowGraph([]);method.ControlFlowGraph=graph;
        var left=new Block{ID=2};var right=new Block{ID=3};var shared=new Block{ID=4};var after=new Block{ID=5};
        graph.Blocks.AddRange([left,right,shared,after]);graph.EntryBlock.Successors=[left,right];
        left.Predecessors=[graph.EntryBlock];right.Predecessors=[graph.EntryBlock];
        left.Successors=[shared];right.Successors=[shared];shared.Predecessors=[left,right];shared.Successors=[after];
        after.Predecessors=[shared];after.Successors=[graph.ExitBlock];graph.ExitBlock.Predecessors=[after];
        var allocation=new Instruction(4,OpCode.Newobj,obj,metadata);
        var construct=new Instruction(5,OpCode.CallVoid,baseCtor,obj,argument){NativeDirectCallTarget=0x1234,
            NativeVirtualDispatch=shape=="virtual"};
        left.Instructions=[new(0,OpCode.Move,metadata,a),new(1,OpCode.Jump,shared)];
        right.Instructions=[new(2,OpCode.Move,metadata,b),new(3,OpCode.Jump,shared)];
        shared.Instructions=[allocation,construct,new(6,OpCode.Move,result,obj),new(7,OpCode.Jump,after)];
        after.Instructions=[new(8,OpCode.Return,result)];
        if(shape=="unknown-edge")right.Instructions.RemoveAt(0);
        if(shape=="duplicate-definition")right.Instructions.Insert(1,new(9,OpCode.Move,metadata,a));
        if(shape=="effect-between-allocation-and-constructor")shared.Instructions.Insert(1,new(9,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape=="callback-suffix")shared.Instructions.Insert(3,new(9,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape=="late-argument")
        {method.ParameterLocals=[];shared.Instructions.Insert(1,new(9,OpCode.Move,argument,new StringLiteral("late")));}
        if(shape=="cycle"){after.Successors.Add(left);left.Predecessors.Add(after);}
        if(shape=="conditional-edge")left.Successors.Add(after);
        if(shape=="instruction-target")left.Instructions[^1].SetOperand(0,allocation);
        if(shape=="phi")after.Instructions.Insert(0,new(9,OpCode.Phi,result,obj));
        var blocks=graph.Blocks.ToArray();var instructions=graph.Instructions.ToArray();
        Assert.That(MergedAllocationRecovery.Recover(method,shared),Is.EqualTo(expected));
        if(!expected)
        {
            Assert.That(graph.Blocks,Is.EqualTo(blocks));Assert.That(graph.Instructions,Is.EqualTo(instructions));
            Assert.That(allocation.Operands[1],Is.SameAs(metadata));Assert.That(construct.Operands[0],Is.SameAs(baseCtor));
            Assert.That(shared.Predecessors,Is.EqualTo(new[]{left,right}));return;
        }
        Assert.That(graph.Blocks,Does.Not.Contain(shared));Assert.That(after.Predecessors,Has.Count.EqualTo(2));
        foreach(var edge in new[]{left,right})
        {
            var copy=edge.Successors.Single();var chosen=edge==left?a:b;var ctor=edge==left?ctorA:ctorB;
            Assert.That(edge.Instructions[^1].Operands[0],Is.SameAs(copy));
            Assert.That(copy.Instructions[0].Operands[1],Is.SameAs(chosen));
            Assert.That(copy.Instructions[1].Operands[0],Is.SameAs(ctor));
            Assert.That(copy.Instructions[1].NativeDirectCallTarget,Is.EqualTo(0x1234));
            Assert.That(IlGenerator.FindConstructorCall(method,copy.Instructions[0]),Is.SameAs(copy.Instructions[1]));
            Assert.That(copy.Successors.Single(),Is.SameAs(after));
            Assert.That(copy.Predecessors.Single(),Is.SameAs(edge));
        }
        Assert.That(graph.Instructions.Count(i=>i.OpCode==OpCode.Newobj),Is.EqualTo(2));
    }
}
