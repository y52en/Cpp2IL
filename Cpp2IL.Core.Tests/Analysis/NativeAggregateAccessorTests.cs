using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeAggregateAccessorTests
{
    [TestCase("whole",true)] [TestCase("component",true)]
    [TestCase("wrong-lane",false)] [TestCase("missing-lane",false)]
    [TestCase("offset",false)] [TestCase("private",false)] [TestCase("virtual",false)]
    [TestCase("partial",false)] [TestCase("write",false)] [TestCase("unknown-receiver",false)]
    [TestCase("same-owner",false)] [TestCase("component-write",false)]
    public void ExactAggregateLayoutAndReadOnlyExtractionPreserveNullCheckedApi(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="UnityEngine.Vector2");
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","VectorOwner",t.SystemObjectType,TypeAttributes.Public);
        var callerType=new InjectedTypeAnalysisContext(owner.DeclaringAssembly,"Test","VectorConsumer",t.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("position",vector,FieldAttributes.Private);field.Offset=24;
        var getter=owner.InjectMethodContext("GetPosition",vector,shape=="private"?MethodAttributes.Private:MethodAttributes.Public,[]);
        if(shape=="virtual")getter.Attributes|=MethodAttributes.Virtual;
        var reads=new List<NativeFieldLoadProofs.Read>{new("fp",0,4,24,0),new("fp",1,4,28,0)};
        if(shape=="wrong-lane")reads[1]=reads[1] with{Register=2};
        if(shape=="missing-lane")reads.RemoveAt(1);
        if(shape=="offset")reads[1]=reads[1] with{Offset=32};
        var contract=NativeAggregateFieldAccessorRecovery.Prove(getter,field,reads);
        if(shape is "wrong-lane" or "missing-lane" or "offset" or "private" or "virtual")
        {Assert.That(contract,Is.Null);return;}
        Assert.That(contract,Is.Not.Null);Assert.That(contract!.Size,Is.EqualTo(8));
        var receiver=new LocalVariable("obj",new Register(null,"obj"),shape=="unknown-receiver"?null:owner);
        var root=new FieldReference(field,receiver,24);
        var component=shape is "component" or "component-write";
        var x=vector.Fields.Single(f=>!f.IsStatic && f.Offset==0);
        var access=component?new FieldReference(x,receiver,0){Parent=root}:root;
        var result=new LocalVariable("result",new Register(null,"result"),component?x.FieldType:vector);
        var width=shape=="partial"?4:component?4:8;
        var instruction=shape is "write" or "component-write"?new Instruction(0,OpCode.Move,access,result){NativeWriteSize=width}
            :new Instruction(0,OpCode.Move,result,access){NativeReadSize=width};
        var caller=new InjectedMethodAnalysisContext(shape=="same-owner"?owner:callerType,"Read",result.Type!,MethodAttributes.Public|MethodAttributes.Static,[]);
        caller.ControlFlowGraph=new([instruction,new(1,OpCode.Return,result)]);caller.Locals=[receiver,result];caller.ParameterLocals=[receiver];
        var contracts=new Dictionary<FieldAnalysisContext,NativeAggregateFieldAccessorRecovery.Contract>{{field,contract}};
        Assert.That(NativeAggregateFieldAccessorRecovery.Recover(caller,contracts),Is.EqualTo(expected?1:0));
        if(!expected){Assert.That(instruction.OpCode,Is.EqualTo(OpCode.Move));Assert.That(caller.Locals.Count,Is.EqualTo(2));return;}
        var call=caller.ControlFlowGraph.Instructions.Single(i=>i.OpCode==OpCode.Call);
        Assert.That(call.Operands[0],Is.SameAs(getter));Assert.That(call.NativeNullCheckedCall,Is.True);Assert.That(call.NativeVirtualDispatch,Is.False);
        if(component)
        {
            Assert.That(instruction.Operands[1],Is.TypeOf<FieldReference>());
            var read=(FieldReference)instruction.Operands[1];Assert.That(read.Parent,Is.Null);
            Assert.That(read.Local,Is.SameAs(call.Operands[1]));Assert.That(caller.Locals.Count,Is.EqualTo(3));
        }
        else Assert.That(instruction,Is.SameAs(call));
    }
}
