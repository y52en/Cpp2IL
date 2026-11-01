using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StructuralConstructorRecoveryTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("valid",true)]
    [TestCase("wrong-expression",false)]
    [TestCase("reversed-arguments",false)]
    [TestCase("missing-leaf",false)]
    [TestCase("callback",false)]
    [TestCase("integer-division",false)]
    [TestCase("ambiguous",false)]
    [TestCase("wrong-field-parent",false)]
    [TestCase("late-argument",false)]
    [TestCase("changed-after-expression",false)]
    [TestCase("unknown-native-width",false)]
    [TestCase("constructor-callback",false)]
    [TestCase("constructor-duplicate-leaf",false)]
    public void OnlyCompleteAggregateAndIdenticalNativeExpressionAreReconstructed(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(a=>a.FullName=="UnityEngine.Vector3");
        var leaves=vector.Fields.Where(f=>!f.IsStatic).OrderBy(f=>f.Offset).ToArray();
        Assert.That(leaves.Length,Is.EqualTo(3));
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","StructuralCtor",t.SystemObjectType,TypeAttributes.Public);
        var stored=owner.InjectFieldContext("vector",vector,FieldAttributes.Public);
        var other=owner.InjectFieldContext("other",vector,FieldAttributes.Public);
        var ratio=owner.InjectFieldContext("ratio",t.SystemSingleType,FieldAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,vector);
        var baseCtor=t.SystemObjectType.Methods.First(m=>m.Name==".ctor" && m.Parameters.Count==0);
        var self=Local("this",owner);self.IsThis=true;
        var parameter=Local("arg",vector);ctor.ParameterLocals=[self,parameter];
        FieldReference Nested(FieldAnalysisContext parent,LocalVariable root,int n)=>new(leaves[n],root,leaves[n].Offset){Parent=new(parent,root,16)};
        var temps=leaves.Select((_,n)=>Local("p"+n,t.SystemSingleType)).ToArray();
        var computed=Local("ratio",shape=="integer-division"?t.SystemInt32Type:t.SystemSingleType);
        var instructions=new List<Instruction>{new(0,OpCode.CallVoid,baseCtor,self)};
        for(var n=0;n<3;n++)instructions.Add(new(1+n,OpCode.Move,temps[n],new FieldReference(leaves[n],parameter,leaves[n].Offset)));
        instructions.Add(new(4,OpCode.Divide,computed,temps[0],temps[1]){NativeFloatingPointSize=shape=="unknown-native-width"?0:4});
        for(var n=0;n<3;n++)instructions.Add(new(5+n,OpCode.Move,Nested(stored,self,n),temps[n]));
        instructions.Add(new(8,OpCode.Move,new FieldReference(ratio,self,32),computed));
        if(shape=="constructor-callback")instructions.Add(new(10,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="constructor-duplicate-leaf")instructions.Add(new(10,OpCode.Move,Nested(stored,self,0),temps[0]));
        instructions.Add(new(9,OpCode.Return));ctor.ControlFlowGraph=new(instructions);
        var template=StructuralConstructorRecovery.Extract(ctor);
        if(shape is "integer-division" or "unknown-native-width" or "constructor-callback" or "constructor-duplicate-leaf")
        {Assert.That(template,Is.Null);return;}
        Assert.That(template,Is.Not.Null);
        var caller=new InjectedMethodAnalysisContext(owner,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,
            [t.SystemSingleType,t.SystemSingleType,t.SystemSingleType]);
        var values=Enumerable.Range(0,3).Select(n=>Local("a"+n,t.SystemSingleType)).ToArray();caller.ParameterLocals=[..values];
        var result=Local("result",t.SystemSingleType);var obj=Local("obj",owner);
        var allocation=new Instruction(12,OpCode.Newobj,obj,owner);var call=new Instruction(13,OpCode.CallVoid,baseCtor,obj);
        var operation=new Instruction(10,shape=="wrong-expression"?OpCode.Multiply:OpCode.Divide,result,
            values[shape=="reversed-arguments"?1:0],values[shape=="reversed-arguments"?0:1]){NativeFloatingPointSize=4};
        var body=new List<Instruction>{operation,allocation,call};
        if(shape=="changed-after-expression")body.Insert(1,new(11,OpCode.Move,values[0],new FloatLiteral(100)));
        if(shape=="late-argument")body.Insert(0,new(11,OpCode.Move,values[0],new FloatLiteral(1)));
        if(shape=="late-argument"){body.Remove(operation);body.Insert(3,operation);}
        for(var n=0;n<(shape=="missing-leaf"?2:3);n++)body.Add(new(14+n,OpCode.Move,Nested(shape=="wrong-field-parent"?other:stored,obj,n),values[n]));
        if(shape=="callback")body.Insert(4,new(18,OpCode.CallVoid,new StringLiteral("callback")));
        body.Add(new(19,OpCode.Move,new FieldReference(ratio,obj,32),result));body.Add(new(20,OpCode.Return));
        caller.ControlFlowGraph=new(body);caller.Locals=[..values,result,obj];
        Assert.That(StructuralConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template!,template!]:[template!]),Is.EqualTo(expected));
        if(!expected){Assert.That(call.Operands[0],Is.SameAs(baseCtor));return;}
        Assert.That(call.Operands[0],Is.SameAs(ctor));
        var argument=(LocalVariable)call.Operands[2];Assert.That(argument.Type,Is.SameAs(vector));
        var prep=caller.ControlFlowGraph.Instructions.TakeWhile(i=>!ReferenceEquals(i,allocation)).ToArray();
        Assert.That(prep.Count(i=>i.Operands.Count==2 && i.Operands[1] is DefaultStructValue),Is.EqualTo(1));
        Assert.That(prep.Count(i=>i.Operands.Count>0 && i.Operands[0] is FieldReference),Is.EqualTo(3));
        Assert.That(operation.OpCode,Is.EqualTo(OpCode.Divide));
        Assert.That(body.Where(i=>i.Index>=14 && i.Index<=19).All(i=>i.OpCode==OpCode.Nop),Is.True);
    }
}
