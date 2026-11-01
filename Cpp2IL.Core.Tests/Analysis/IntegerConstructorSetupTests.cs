using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IntegerConstructorSetupTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("add32",true)]
    [TestCase("subtract32",true)]
    [TestCase("multiply32",true)]
    [TestCase("add64",true)]
    [TestCase("enum-input",true)]
    [TestCase("chain",true)]
    [TestCase("unknown-width",false)]
    [TestCase("wrong-width",false)]
    [TestCase("widened-multiply",false)]
    [TestCase("divide",false)]
    [TestCase("shift",false)]
    [TestCase("floating",false)]
    [TestCase("reference-input",false)]
    [TestCase("field-read",false)]
    [TestCase("late-input",false)]
    [TestCase("callback",false)]
    [TestCase("alias",false)]
    [TestCase("reassigned",false)]
    [TestCase("ambiguous",false)]
    public void OnlyExactNonthrowingIntegerWidthsAndAvailableInputsCanMoveBeforeAllocation(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var scalar=shape=="add64"?t.SystemInt64Type:shape=="floating"?t.SystemSingleType:t.SystemInt32Type;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","IntegerSetup",t.SystemObjectType,TypeAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,scalar);
        var field=owner.InjectFieldContext("value",scalar,FieldAttributes.Public);field.Offset=16;
        var root=new InjectedMethodAnalysisContext(t.SystemObjectType,".ctor",t.SystemVoidType,MethodAttributes.Public,[]);
        root.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(true));
        var self=Local("this",owner);self.IsThis=true;var value=Local("value",scalar);ctor.ParameterLocals=[self,value];
        var width=shape=="add64"?8:4;
        ctor.ControlFlowGraph=new([new(0,OpCode.CallVoid,root,self),
            new Instruction(1,OpCode.Move,new FieldReference(field,self,16),value){NativeWriteSize=width},new(2,OpCode.Return)]);
        var template=InlinedConstructorRecovery.Extract(ctor)!;Assert.That(template,Is.Not.Null);
        var inputType=scalar;
        if(shape=="enum-input")inputType=app.Assemblies.SelectMany(a=>a.Types).First(x=>x.IsEnumType&&ReferenceEquals(x.EnumUnderlyingType,t.SystemInt32Type));
        if(shape=="reference-input")inputType=t.SystemObjectType;
        var caller=owner.InjectMethodContext("Create",owner,MethodAttributes.Static|MethodAttributes.Public,inputType);
        var input=Local("input",inputType);caller.ParameterLocals=shape=="late-input"?[]:[input];
        var obj=Local("obj",owner);var result=Local("result",scalar);var intermediate=Local("intermediate",scalar);
        var allocation=new Instruction(10,OpCode.Newobj,obj,owner);
        var opcode=shape switch{"subtract32"=>OpCode.Subtract,"multiply32"or"widened-multiply"=>OpCode.Multiply,
            "divide"=>OpCode.Divide,"shift"=>OpCode.ShiftLeft,_=>OpCode.Add};
        IOperand source=shape=="field-read"?new FieldReference(field,Local("holder",owner),16):input;
        var arithmetic=new Instruction(11,opcode,shape=="chain"?intermediate:result,source,new Immediate(1))
            {NativeArithmeticSize=shape=="unknown-width"?0:shape=="wrong-width"?8:width,NativeMultiplyInputSize=shape=="widened-multiply"?4:0};
        var chain=new Instruction(12,OpCode.Subtract,result,intermediate,new Immediate(2)){NativeArithmeticSize=width};
        var call=new Instruction(13,OpCode.CallVoid,root,obj);
        var store=new Instruction(14,OpCode.Move,new FieldReference(field,obj,16),result){NativeWriteSize=width};
        var instructions=new List<Instruction>();
        if(shape=="reassigned")instructions.Add(new(9,OpCode.Move,result,new Immediate(0)));
        instructions.Add(allocation);
        if(shape=="late-input")instructions.Add(new(9,OpCode.Move,input,new Immediate(1)));
        if(shape=="callback")instructions.Add(new(9,OpCode.CallVoid,new StringLiteral("effect")));
        instructions.Add(arithmetic);if(shape=="chain")instructions.Add(chain);
        instructions.AddRange([call,store]);
        if(shape=="alias")instructions.Add(new(15,OpCode.CallVoid,new StringLiteral("alias"),new AddressOf(result)));
        instructions.Add(new(16,OpCode.Return,obj));caller.ControlFlowGraph=new(instructions);
        var before=caller.ControlFlowGraph.Instructions.ToArray();var texts=before.Select(i=>i.ToString()).ToArray();
        Assert.That(InlinedConstructorRecovery.RecoverScalarSetup(caller,allocation,shape=="ambiguous"?[template,template]:[template]),Is.EqualTo(expected));
        if(!expected)
        {
            Assert.That(caller.ControlFlowGraph.Instructions,Is.EqualTo(before));
            Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(texts));return;
        }
        Assert.That(call.Operands[0],Is.SameAs(ctor));Assert.That(call.Operands[2],Is.SameAs(result));
        var after=caller.ControlFlowGraph.Instructions;
        Assert.That(after.IndexOf(arithmetic),Is.LessThan(after.IndexOf(allocation)));
        if(shape=="chain")
        {Assert.That(after.IndexOf(chain),Is.GreaterThan(after.IndexOf(arithmetic)));Assert.That(after.IndexOf(chain),Is.LessThan(after.IndexOf(allocation)));}
        Assert.That(store.OpCode,Is.EqualTo(OpCode.Nop));
        Assert.That(arithmetic.NativeArithmeticSize,Is.EqualTo(width));
    }
}
