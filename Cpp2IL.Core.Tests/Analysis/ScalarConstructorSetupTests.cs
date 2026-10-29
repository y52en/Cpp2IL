using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ScalarConstructorSetupTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("exact",true)]
    [TestCase("linear-block",true)]
    [TestCase("reordered-only",true)]
    [TestCase("integer-conversion",false)]
    [TestCase("no-ancestor-proof",false)]
    [TestCase("unknown-store-width",false)]
    [TestCase("unknown-template-width",false)]
    [TestCase("overlap",false)]
    [TestCase("ambiguous",false)]
    [TestCase("late-input",false)]
    [TestCase("effect",false)]
    [TestCase("destination-reassigned",false)]
    [TestCase("destination-used-before",false)]
    [TestCase("destination-addressed",false)]
    [TestCase("type-initializer",false)]
    [TestCase("finalizer",false)]
    [TestCase("explicit-layout",false)]
    [TestCase("side-entry",false)]
    public void PureFloatSetupIsCommittedOnlyWithACompleteUnambiguousScalarConstructor(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","ScalarParent",t.SystemObjectType,TypeAttributes.Public);
        var owner=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","ScalarChild",parent,TypeAttributes.Public);
        var flag=parent.InjectFieldContext("flag",t.SystemBooleanType,FieldAttributes.Public);flag.Offset=shape=="overlap"?20:16;
        var ratio=owner.InjectFieldContext("ratio",t.SystemSingleType,FieldAttributes.Public);ratio.Offset=20;
        var root=new InjectedMethodAnalysisContext(t.SystemObjectType,".ctor",t.SystemVoidType,MethodAttributes.Public,[]);
        root.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(shape!="no-ancestor-proof"));
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemBooleanType,t.SystemSingleType);
        var self=Local("this",owner);self.IsThis=true;var b=Local("b",t.SystemBooleanType);var f=Local("f",t.SystemSingleType);
        ctor.ParameterLocals=[self,b,f];
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,root,self),
            new Instruction(1,OpCode.Move,new FieldReference(ratio,self,20),f){NativeWriteSize=shape=="unknown-template-width"?0:4},
            new Instruction(2,OpCode.Move,new FieldReference(flag,self,flag.Offset),b){NativeWriteSize=1},new(3,OpCode.Return)]);
        var extracted=InlinedConstructorRecovery.Extract(ctor);
        if(shape=="no-ancestor-proof")Assert.That(extracted,Is.Null);
        var template=extracted??new InlinedConstructorRecovery.Template(ctor,
            [new(ratio,1){NativeWidth=4},new(flag,0){NativeWidth=1}],root){BaseArguments=[]};
        var caller=owner.InjectMethodContext("Create",owner,MethodAttributes.Public|MethodAttributes.Static,t.SystemDoubleType);
        var input=Local("input",t.SystemDoubleType);caller.ParameterLocals=shape=="late-input"?[]:[input];
        var obj=Local("obj",owner);var converted=Local("converted",shape=="integer-conversion"?t.SystemInt32Type:t.SystemSingleType);
        var allocation=new Instruction(10,OpCode.Newobj,obj,owner);
        var conversion=new Instruction(11,OpCode.NumericConvert,converted,converted.Type!,t.SystemDoubleType,input);
        var call=new Instruction(12,OpCode.CallVoid,root,obj);
        var a=new Instruction(13,OpCode.Move,new FieldReference(flag,obj,flag.Offset),new Immediate(1)){NativeWriteSize=1};
        var z=new Instruction(14,OpCode.Move,new FieldReference(ratio,obj,20),converted){NativeWriteSize=shape=="unknown-store-width"?0:4};
        var instructions=new List<Instruction>();
        if(shape=="destination-reassigned")instructions.Add(new(5,OpCode.Move,converted,new FloatLiteral(3)));
        if(shape=="destination-used-before")instructions.Add(new(5,OpCode.CallVoid,new StringLiteral("use"),converted));
        if(shape=="reordered-only")instructions.Add(conversion);
        instructions.Add(allocation);
        if(shape=="late-input")instructions.Add(new(6,OpCode.Move,input,new DoubleLiteral(1)));
        if(shape=="effect")instructions.Add(new(6,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape!="reordered-only")instructions.Add(conversion);
        instructions.AddRange([call,a,z]);
        if(shape=="destination-addressed")instructions.Add(new(15,OpCode.CallVoid,new StringLiteral("alias"),new AddressOf(converted)));
        instructions.Add(new(16,OpCode.Return,obj));
        caller.ControlFlowGraph=new(instructions);
        if(shape is "linear-block" or "side-entry")
        {
            var graph=new ISILControlFlowGraph([]);var left=new Block{ID=2};var right=new Block{ID=3};
            graph.Blocks.AddRange([left,right]);graph.EntryBlock.Successors.Add(left);left.Predecessors.Add(graph.EntryBlock);
            left.Successors.Add(right);right.Predecessors.Add(left);right.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(right);
            left.Instructions.Add(allocation);right.Instructions.AddRange([conversion,call,a,z,new(16,OpCode.Return,obj)]);
            if(shape=="side-entry")
            {
                var bypass=new Block{ID=4};graph.Blocks.Add(bypass);graph.EntryBlock.Successors.Add(bypass);
                bypass.Predecessors.Add(graph.EntryBlock);bypass.Successors.Add(right);right.Predecessors.Add(bypass);
            }
            caller.ControlFlowGraph=graph;
        }
        if(shape=="type-initializer")owner.InjectMethodContext(".cctor",t.SystemVoidType,MethodAttributes.Static|MethodAttributes.Private);
        if(shape=="finalizer")owner.InjectMethodContext("Finalize",t.SystemVoidType,MethodAttributes.Virtual|MethodAttributes.Family);
        if(shape=="explicit-layout")owner.Attributes=(owner.Attributes&~TypeAttributes.LayoutMask)|TypeAttributes.ExplicitLayout;
        var before=caller.ControlFlowGraph.Instructions.ToArray();var texts=before.Select(i=>i.ToString()).ToArray();
        var result=InlinedConstructorRecovery.RecoverScalarSetup(caller,allocation,shape=="ambiguous"?[template,template]:[template]);
        Assert.That(result,Is.EqualTo(expected));
        if(!expected)
        {
            Assert.That(caller.ControlFlowGraph.Instructions,Is.EqualTo(before));
            Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(texts));
            return;
        }
        Assert.That(call.Operands[0],Is.SameAs(ctor));
        Assert.That(call.Operands[2],Is.TypeOf<Immediate>());Assert.That(((Immediate)call.Operands[2]).Value,Is.EqualTo(1));
        Assert.That(call.Operands[3],Is.SameAs(converted));
        Assert.That(caller.ControlFlowGraph.Instructions.IndexOf(conversion),Is.LessThan(caller.ControlFlowGraph.Instructions.IndexOf(allocation)));
        Assert.That(a.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(z.OpCode,Is.EqualTo(OpCode.Nop));
    }
}
