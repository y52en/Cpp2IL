using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlinedConstructorRecoveryTests
{
    private static LocalVariable Local(string name,TypeAnalysisContext type) => new(name,new Register(null,name),type);

    private static (InjectedTypeAnalysisContext Type,InjectedMethodAnalysisContext Ctor,FieldAnalysisContext A,FieldAnalysisContext B,MethodAnalysisContext Base) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var types=app.SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Derived",types.SystemObjectType,TypeAttributes.Public);
        var ctor=type.InjectMethodContext(".ctor",types.SystemVoidType,MethodAttributes.Public,types.SystemInt32Type,types.SystemSingleType);
        var a=type.InjectFieldContext("a",types.SystemInt32Type,FieldAttributes.Public);
        var b=type.InjectFieldContext("b",types.SystemSingleType,FieldAttributes.Public);
        var baseCtor=types.SystemObjectType.Methods.First(m=>m.Name==".ctor"&&m.Parameters.Count==0);
        var self=Local("this",type);self.IsThis=true;
        var p=Local("p",types.SystemInt32Type);var q=Local("q",types.SystemSingleType);
        ctor.ParameterLocals=[self,p,q];
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,baseCtor,self),
            new(1,OpCode.Move,new FieldReference(b,self,20),q),
            new(2,OpCode.Move,new FieldReference(a,self,16),p),new(3,OpCode.Return)]);
        return(type,ctor,a,b,baseCtor);
    }

    [Test]
    public void CompletePureConstructorExtractsParameterOrderNotFieldOrder()
    {
        var f=Fixture();
        var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        Assert.That(template,Is.Not.Null);
        Assert.That(template.Assignments.Select(a=>a.Parameter),Is.EqualTo(new[]{1,0}));
    }

    [TestCase("call")]
    [TestCase("field-read")]
    [TestCase("duplicate-field")]
    public void UnprovedConstructorEffectsRejectTheTemplate(string shape)
    {
        var f=Fixture();var cfg=f.Ctor.ControlFlowGraph!;
        var block=cfg.Blocks.First(b=>b.Instructions.Any(i=>i.OpCode==OpCode.Move));
        var self=f.Ctor.ParameterLocals[0];
        var effect=shape=="call"?new Instruction(10,OpCode.CallVoid,new StringLiteral("callback"))
            :shape=="field-read"?new Instruction(10,OpCode.Move,Local("loaded",f.A.FieldType),new FieldReference(f.A,self,16))
            :new Instruction(10,OpCode.Move,new FieldReference(f.A,self,16),f.Ctor.ParameterLocals[1]);
        block.Instructions.Insert(0,effect);
        Assert.That(InlinedConstructorRecovery.Extract(f.Ctor),Is.Null);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RestoresTheAllocatedConstructorAndArguments(bool reversedStores)
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        var a=new Instruction(2,OpCode.Move,new FieldReference(f.A,obj,16),new Immediate(42));
        var b=new Instruction(3,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1.5f));
        caller.ControlFlowGraph=new(reversedStores?[allocation,call,b,a,new(4,OpCode.Return)]:[allocation,call,a,b,new(4,OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[template]),Is.True);
        Assert.That(call.Operands[0],Is.SameAs(f.Ctor));
        Assert.That(((Immediate)call.Operands[2]).Value,Is.EqualTo(42));
        Assert.That(((FloatLiteral)call.Operands[3]).Value,Is.EqualTo(1.5f));
        Assert.That(a.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(b.OpCode,Is.EqualTo(OpCode.Nop));
    }

    [TestCase("late-argument")]
    [TestCase("callback")]
    [TestCase("missing-store")]
    [TestCase("ambiguous")]
    public void UnsafeOrAmbiguousCallsiteIsUnchanged(string shape)
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var p=Local("p",f.A.FieldType);
        var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        var list=new List<Instruction>{allocation,call};
        if(shape=="callback") list.Add(new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="late-argument") list.Add(new(2,OpCode.Move,p,new Immediate(42)));
        var a=new Instruction(3,OpCode.Move,new FieldReference(f.A,obj,16),shape=="late-argument"?p:new Immediate(42));list.Add(a);
        if(shape!="missing-store") list.Add(new(4,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1.5f)));
        list.Add(new(5,OpCode.Return));caller.ControlFlowGraph=new(list);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template,template]:[template]),Is.False);
        Assert.That(call.Operands[0],Is.SameAs(f.Base));Assert.That(a.OpCode,Is.EqualTo(OpCode.Move));
    }

    [Test]
    public void EarlierBfsDefinitionOnAnotherPathIsNotAnAvailableArgument()
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var p=Local("p",f.A.FieldType);
        var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        var graph=new ISILControlFlowGraph([]);
        var left=new Block{ID=2};var right=new Block{ID=3};var join=new Block{ID=4};
        graph.Blocks.AddRange([left,right,join]);
        graph.EntryBlock.Successors.AddRange([left,right]);left.Predecessors.Add(graph.EntryBlock);right.Predecessors.Add(graph.EntryBlock);
        left.Successors.Add(join);right.Successors.Add(join);join.Predecessors.AddRange([left,right]);
        join.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(join);
        left.Instructions.Add(new(10,OpCode.Move,p,new Immediate(42)));
        join.Instructions.AddRange([allocation,call,new(2,OpCode.Move,new FieldReference(f.A,obj,16),p),
            new(3,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1.5f)),new(4,OpCode.Return)]);
        caller.ControlFlowGraph=graph;
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[template]),Is.False);
        Assert.That(call.Operands[0],Is.SameAs(f.Base));
    }

    [Test]
    public void LaterCounterUpdateDoesNotInvalidateTheCurrentArgumentValue()
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var counter=Local("counter",f.A.FieldType);
        var allocation=new Instruction(1,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(2,OpCode.CallVoid,f.Base,obj);
        caller.ControlFlowGraph=new([new(0,OpCode.Move,counter,new Immediate(0)),allocation,call,
            new(3,OpCode.Move,new FieldReference(f.A,obj,16),counter),
            new(4,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1.5f)),
            new(5,OpCode.Add,counter,counter,new Immediate(1)),new(6,OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[template]),Is.True);
        Assert.That(call.Operands[2],Is.SameAs(counter));
        Assert.That(caller.ControlFlowGraph.Instructions.Any(i=>i.OpCode==OpCode.Add),Is.True);
    }

    [TestCase(true)]
    [TestCase(false)]
    public void OnlyNonThrowingStructFieldArgumentsCanMoveIntoTheConstructor(bool valueType)
    {
        var f=Fixture();var types=f.Type.AppContext.SystemTypes;
        var data=new InjectedTypeAnalysisContext(f.Type.DeclaringAssembly,"Test","Args",
            valueType?types.SystemValueTypeType:types.SystemObjectType,TypeAttributes.Public);
        var field=data.InjectFieldContext("count",types.SystemInt32Type,FieldAttributes.Public);
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,
            MethodAttributes.Public|MethodAttributes.Static,[data]);
        var parameter=Local("data",data);caller.ParameterLocals=[parameter];
        var obj=Local("obj",f.Type);var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        caller.ControlFlowGraph=new([allocation,call,
            new(2,OpCode.Move,new FieldReference(f.A,obj,16),new FieldReference(field,parameter,4)),
            new(3,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1)),new(4,OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[InlinedConstructorRecovery.Extract(f.Ctor)!]),Is.EqualTo(valueType));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void ReferenceFieldReadsRequireTheCanonicalThisReceiver(bool canonicalThis)
    {
        var f=Fixture();
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public,[]);
        var self=Local("this",f.Type);self.IsThis=true;caller.ParameterLocals=[self];
        var receiver=canonicalThis?self:Local("unproved-this-alias",f.Type);receiver.IsThis=true;
        var obj=Local("obj",f.Type);var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        caller.ControlFlowGraph=new([allocation,call,
            new(2,OpCode.Move,new FieldReference(f.A,obj,16),new FieldReference(f.A,receiver,16)),
            new(3,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1)),new(4,OpCode.Return)]);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[InlinedConstructorRecovery.Extract(f.Ctor)!]),Is.EqualTo(canonicalThis));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void JoinedArgumentRequiresAnAssignmentOnEveryIncomingPath(bool bothPathsAssigned)
    {
        var f=Fixture();var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var p=Local("joined",f.A.FieldType);
        var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        var graph=new ISILControlFlowGraph([]);var left=new Block{ID=2};var right=new Block{ID=3};var join=new Block{ID=4};
        graph.Blocks.AddRange([left,right,join]);graph.EntryBlock.Successors.AddRange([left,right]);
        left.Predecessors.Add(graph.EntryBlock);right.Predecessors.Add(graph.EntryBlock);
        left.Successors.Add(join);right.Successors.Add(join);join.Predecessors.AddRange([left,right]);
        join.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(join);
        left.Instructions.Add(new(10,OpCode.Move,p,new Immediate(1)));
        if(bothPathsAssigned)right.Instructions.Add(new(11,OpCode.Move,p,new Immediate(0)));
        join.Instructions.AddRange([allocation,call,new(2,OpCode.Move,new FieldReference(f.A,obj,16),p),
            new(3,OpCode.Move,new FieldReference(f.B,obj,20),new FloatLiteral(1)),new(4,OpCode.Return)]);
        caller.ControlFlowGraph=graph;
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,[InlinedConstructorRecovery.Extract(f.Ctor)!]),Is.EqualTo(bothPathsAssigned));
    }
}
