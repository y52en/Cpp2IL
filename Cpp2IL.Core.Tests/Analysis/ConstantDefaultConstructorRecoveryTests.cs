using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstantDefaultConstructorRecoveryTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    static (InjectedTypeAnalysisContext Type,InjectedMethodAnalysisContext Ctor,MethodAnalysisContext Base,
        FieldAnalysisContext Number,FieldAnalysisContext Text) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","ConstantDefault",types.SystemObjectType,TypeAttributes.Public);
        var ctor=type.InjectMethodContext(".ctor",types.SystemVoidType,MethodAttributes.Public);
        var number=type.InjectFieldContext("number",types.SystemInt32Type,FieldAttributes.Public);number.Offset=16;
        var text=type.InjectFieldContext("text",types.SystemStringType,FieldAttributes.Public);text.Offset=24;
        var parent=types.SystemObjectType.Methods.First(m=>m.Name==".ctor"&&m.Parameters.Count==0);
        var self=Local("this",type);self.IsThis=true;ctor.ParameterLocals=[self];
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,parent,self),
            new(1,OpCode.Move,new FieldReference(number,self,16),new Immediate(7)),
            new(2,OpCode.Move,new FieldReference(text,self,24),new Immediate(0)),new(3,OpCode.Return)]);
        return(type,ctor,parent,number,text);
    }

    [Test]
    public void ExtractsOnlyCompleteNativeConstantAssignmentsWithoutInventingArguments()
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor);
        Assert.That(template,Is.Not.Null);
        Assert.That(template!.Constructor,Is.SameAs(f.Ctor));
        Assert.That(template.BaseConstructor,Is.SameAs(f.Base));
        Assert.That(template.Assignments.Select(a=>a.Parameter),Is.EqualTo(new[]{-1,-1}));
        Assert.That(template.Assignments.Select(a=>((Immediate)a.Constant!).Value),Is.EqualTo(new long[]{7,0}));
    }

    [TestCase("exact",true)]
    [TestCase("reverse-independent-fields",true)]
    [TestCase("wrong-constant",false)]
    [TestCase("wrong-null",false)]
    [TestCase("missing-store",false)]
    [TestCase("callback",false)]
    [TestCase("ambiguous",false)]
    [TestCase("wrong-width",false)]
    public void FusesOnlyAnUnambiguousExactNativeInitialization(string shape,bool expected)
    {
        var f=Fixture();var template=InlinedConstructorRecovery.Extract(f.Ctor)!;
        var caller=new InjectedMethodAnalysisContext(f.Type,"Caller",f.Ctor.ReturnType,MethodAttributes.Static,[]);
        var obj=Local("obj",f.Type);var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        var call=new Instruction(1,OpCode.CallVoid,f.Base,obj);
        var number=new Instruction(2,OpCode.Move,new MemoryOperand(obj,addend:16),new Immediate(shape=="wrong-constant"?8:7))
            {NativeWriteSize=shape=="wrong-width"?8:4};
        var text=new Instruction(3,OpCode.Move,new MemoryOperand(obj,addend:24),new Immediate(shape=="wrong-null"?1:0)){NativeWriteSize=8};
        var instructions=new List<Instruction>{allocation,call};
        if(shape=="callback")instructions.Add(new(9,OpCode.CallVoid,new StringLiteral("publish")));
        if(shape=="reverse-independent-fields")instructions.AddRange([text,number]);
        else{instructions.Add(number);if(shape!="missing-store")instructions.Add(text);}
        instructions.Add(new(4,OpCode.Return));caller.ControlFlowGraph=new(instructions);
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template,template]:[template]),Is.EqualTo(expected));
        Assert.That(call.Operands[0],Is.SameAs(expected?f.Ctor:f.Base));
        Assert.That(call.Operands.Count,Is.EqualTo(2));
        Assert.That(number.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
        Assert.That(text.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
    }

    [TestCase("callback")]
    [TestCase("duplicate-field")]
    [TestCase("field-read")]
    [TestCase("non-null-reference")]
    public void RejectsAnUnprovedNativeConstructorTemplate(string shape)
    {
        var f=Fixture();var block=f.Ctor.ControlFlowGraph!.Blocks.Single(b=>b.Instructions.Any(i=>i.OpCode==OpCode.Move));
        var self=f.Ctor.ParameterLocals[0];
        if(shape=="non-null-reference")
            block.Instructions.Single(i=>i.Operands.FirstOrDefault()is FieldReference field&&field.Field==f.Text).SetOperand(1,new Immediate(1));
        else
        {
            var extra=shape=="callback"?new Instruction(20,OpCode.CallVoid,new StringLiteral("publish")):
                shape=="duplicate-field"?new Instruction(20,OpCode.Move,new FieldReference(f.Number,self,16),new Immediate(7)):
                new Instruction(20,OpCode.Move,Local("read",f.Number.FieldType),new FieldReference(f.Number,self,16));
            block.Instructions.Insert(0,extra);
        }
        Assert.That(InlinedConstructorRecovery.Extract(f.Ctor),Is.Null);
    }
}
