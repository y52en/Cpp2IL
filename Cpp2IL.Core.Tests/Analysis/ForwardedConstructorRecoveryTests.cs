using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardedConstructorRecoveryTests
{
    static LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);

    [TestCase("valid",true)]
    [TestCase("alias",true)]
    [TestCase("ancestor",true)]
    [TestCase("reordered",false)]
    [TestCase("extra-effect",false)]
    [TestCase("virtual",false)]
    [TestCase("wrong-base",false)]
    [TestCase("wrong-type",false)]
    [TestCase("missing-argument",false)]
    [TestCase("duplicate-call",false)]
    [TestCase("caller-effect",false)]
    [TestCase("caller-late-value",false)]
    [TestCase("ambiguous",false)]
    public void RebindsOnlyCompleteExactParameterForwarding(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Parent",t.SystemObjectType,TypeAttributes.Public);
        var owner=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","Child",parent,TypeAttributes.Public);
        var baseCtor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemStringType);
        if(shape=="ancestor")
        {
            var ancestor=new InjectedTypeAnalysisContext(parent.DeclaringAssembly,"Test","Ancestor",t.SystemObjectType,TypeAttributes.Public);
            parent.OverrideBaseType=ancestor;
            baseCtor=ancestor.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemStringType);
        }
        var ctor=owner.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemStringType);
        var self=Local("this",owner);self.IsThis=true;var a=Local("a",t.SystemStringType);var b=Local("b",t.SystemStringType);
        ctor.ParameterLocals=[self,a,b];
        var call=new Instruction(0,OpCode.CallVoid,baseCtor,self,shape=="reordered"?b:a,shape=="reordered"?a:b)
            {NativeVirtualDispatch=shape=="virtual"};
        if(shape=="wrong-base")call.SetOperand(0,t.SystemObjectType.Methods.First(m=>m.Name==".ctor" && m.Parameters.Count==0));
        if(shape=="wrong-type")b.Type=t.SystemInt32Type;
        if(shape=="missing-argument")call.RemoveOperandAt(3);
        ctor.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        var body=ctor.ControlFlowGraph.Blocks.Single(block=>block.Instructions.Contains(call));
        if(shape=="extra-effect")body.Instructions.Insert(0,new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="duplicate-call")body.Instructions.Insert(1,new(2,OpCode.CallVoid,baseCtor,self,a,b));
        var template=ForwardedConstructorRecovery.Extract(ctor);
        if(shape is "reordered" or "extra-effect" or "virtual" or "wrong-base" or "wrong-type" or "missing-argument" or "duplicate-call")
        {Assert.That(template,Is.Null);return;}
        Assert.That(template,Is.Not.Null);
        var caller=new InjectedMethodAnalysisContext(owner,"Create",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[t.SystemStringType,t.SystemStringType]);
        var x=Local("x",t.SystemStringType);var y=Local("y",t.SystemStringType);caller.ParameterLocals=[x,y];
        var obj=Local("obj",owner);var alias=Local("alias",owner);
        var allocation=new Instruction(10,OpCode.Newobj,obj,owner);
        var construct=new Instruction(12,OpCode.CallVoid,baseCtor,shape=="alias"?alias:obj,x,y);
        caller.ControlFlowGraph=new([allocation,construct,new(13,OpCode.Return)]);caller.Locals=[obj,alias,x,y];
        var callerBody=caller.ControlFlowGraph.Blocks.Single(block=>block.Instructions.Contains(allocation));
        if(shape=="alias")callerBody.Instructions.Insert(1,new(11,OpCode.Move,alias,obj));
        if(shape=="caller-effect")callerBody.Instructions.Insert(1,new(11,OpCode.CallVoid,new StringLiteral("effect")));
        if(shape=="caller-late-value")callerBody.Instructions.Insert(1,new(11,OpCode.Move,x,new StringLiteral("late")));
        Assert.That(ForwardedConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template!,template!]:[template!]),Is.EqualTo(expected));
        Assert.That(construct.Operands[0],Is.SameAs(expected?ctor:baseCtor));
        Assert.That(construct.Operands[2],Is.SameAs(x));Assert.That(construct.Operands[3],Is.SameAs(y));
    }
}
