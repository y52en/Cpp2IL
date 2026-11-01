using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArgumentForwardingConstructorTests
{
    [TestCase("initializer",true)]
    [TestCase("allocation",true)]
    [TestCase("alias",true)]
    [TestCase("wrong-constant",false)]
    [TestCase("ambiguous",false)]
    [TestCase("extra-effect",false)]
    [TestCase("field-store",false)]
    [TestCase("wrong-base",false)]
    [TestCase("parameter-type",false)]
    [TestCase("virtual",false)]
    [TestCase("missing-argument",false)]
    [TestCase("caller-effect",false)]
    [TestCase("caller-late-value",false)]
    [TestCase("missing-self",false)]
    public void ReconstructsOnlyWholeParameterAndConstantForwardingContracts(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;var assembly=t.SystemObjectType.DeclaringAssembly;
        var root=new InjectedTypeAnalysisContext(assembly,"Test","Root",t.SystemObjectType,TypeAttributes.Public);
        var parent=new InjectedTypeAnalysisContext(assembly,"Test","Parent",root,TypeAttributes.Public);
        var child=new InjectedTypeAnalysisContext(assembly,"Test","Child",parent,TypeAttributes.Public);
        var target=root.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemInt32Type,t.SystemBooleanType);
        var constructor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemBooleanType);
        LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new Register(null,name),type);
        var self=Local("this",parent);self.IsThis=true;var input=Local("input",t.SystemStringType);var flag=Local("flag",t.SystemBooleanType);
        constructor.ParameterLocals=[self,input,flag];
        var forwarding=new Instruction(0,OpCode.CallVoid,target,self,input,new Immediate(14),flag){NativeVirtualDispatch=shape=="virtual"};
        if(shape=="parameter-type")input.Type=t.SystemInt32Type;
        if(shape=="wrong-base")forwarding.SetOperand(0,parent.InjectMethodContext("Other",t.SystemVoidType,MethodAttributes.Public));
        if(shape=="missing-argument")forwarding.RemoveOperandAt(4);
        constructor.ControlFlowGraph=new([forwarding,new(1,OpCode.Return)]);
        var home=constructor.ControlFlowGraph.Blocks.Single(b=>b.Instructions.Contains(forwarding));
        if(shape=="extra-effect")home.Instructions.Insert(0,new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="field-store")home.Instructions.Insert(0,new(2,OpCode.Move,new MemoryOperand(self.Register,addend:32),new Immediate(1)));
        var template=ArgumentForwardingConstructorRecovery.Extract(constructor);
        if(shape is "extra-effect" or "field-store" or "wrong-base" or "parameter-type" or "virtual" or "missing-argument")
        {Assert.That(template,Is.Null);return;}
        Assert.That(template,Is.Not.Null);
        parent.PutExtraData(ArgumentForwardingConstructorRecovery.CacheKey,shape=="ambiguous"?new[]{template!,template!}:new[]{template!});
        var allocation=shape is "allocation" or "alias" or "caller-effect" or "caller-late-value";
        var caller=allocation?parent.InjectMethodContext("Make",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,t.SystemStringType)
            :child.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType);
        var receiver=Local("this",child);receiver.IsThis=!allocation;
        var argument=Local("arg",t.SystemStringType);caller.ParameterLocals=allocation?[argument]:[receiver,argument];
        if(shape=="missing-self")receiver.IsThis=false;
        var alias=Local("alias",parent);
        var call=new Instruction(12,OpCode.CallVoid,target,shape=="alias"?alias:receiver,argument,
            new Immediate(shape=="wrong-constant"?15:14),new Immediate(1));
        var instructions=new System.Collections.Generic.List<Instruction>();
        if(allocation)instructions.Add(new(10,OpCode.Newobj,receiver,parent));
        if(shape=="alias")instructions.Add(new(11,OpCode.Move,alias,receiver));
        if(shape=="caller-effect")instructions.Add(new(11,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="caller-late-value")instructions.Add(new(11,OpCode.Move,argument,new StringLiteral("late")));
        instructions.Add(call);instructions.Add(new(13,OpCode.Return));caller.ControlFlowGraph=new(instructions);
        var before=caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(ArgumentForwardingConstructorRecovery.Run(caller)>0,Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(call.Operands[0],Is.SameAs(constructor));Assert.That(call.Operands.Count,Is.EqualTo(4));
            Assert.That(call.Operands[2],Is.SameAs(argument));Assert.That(((Immediate)call.Operands[3]).Value,Is.EqualTo(1));
        }
        else Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
    }
}
