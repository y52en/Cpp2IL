using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardedConstantConstructorTests
{
    [TestCase("valid",true)]
    [TestCase("wrong-value",false)]
    [TestCase("wrong-width",false)]
    [TestCase("integer-bits-not-float",false)]
    [TestCase("different-base-target",false)]
    [TestCase("callback-before-base",false)]
    [TestCase("store-after-base",false)]
    [TestCase("negative-zero",false)]
    public void ConstantInitializersForwardTheExactObservableBaseCall(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var root=app.SystemTypes.SystemObjectType;
        var parent=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","ObservableBase",root,TypeAttributes.Public);
        var owner=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","Derived",parent,TypeAttributes.Public);
        var baseCtor=parent.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public);
        var field=owner.InjectFieldContext("Speed",app.SystemTypes.SystemSingleType,FieldAttributes.Public);field.Offset=44;
        var self=new LocalVariable("this",new(null,"X0"),owner){IsThis=true};
        var sourceStore=new Instruction(0,OpCode.Move,new FieldReference(field,self,44),new FloatLiteral(1)){NativeWriteSize=4};
        ctor.ControlFlowGraph=new([sourceStore,new(1,OpCode.CallVoid,baseCtor,self),new(2,OpCode.Return)]);
        var template=ConstantFieldConstructorRecovery.Extract(ctor);
        Assert.That(template,Is.Not.Null);
        Assert.That(template!.BaseConstructor,Is.SameAs(baseCtor));
        owner.PutExtraData(ConstantFieldConstructorRecovery.CacheKey,new[]{template});
        var obj=new LocalVariable("obj",new(null,"obj"),owner);
        IOperand value=shape switch {"integer-bits-not-float"=>new Immediate(0x3f800000),
            "wrong-value"=>new FloatLiteral(2),"negative-zero"=>new FloatLiteral(-0.0f),_=>new FloatLiteral(1)};
        var store=new Instruction(1,OpCode.Move,new FieldReference(field,obj,44),value){NativeWriteSize=shape=="wrong-width"?8:4};
        var target=shape=="different-base-target"?parent.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public):baseCtor;
        var call=new Instruction(2,OpCode.CallVoid,target,obj);
        var instructions=new System.Collections.Generic.List<Instruction>{new(0,OpCode.Newobj,obj,owner),store,call,new(3,OpCode.Return)};
        if(shape=="callback-before-base")instructions.Insert(2,new(4,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="store-after-base")instructions=[instructions[0],call,store,instructions[^1]];
        var caller=owner.InjectMethodContext("Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        caller.ControlFlowGraph=new(instructions);
        Assert.That(ConstantFieldConstructorRecovery.Run(caller),Is.EqualTo(expected?1:0));
        Assert.That(call.Operands[0],Is.SameAs(expected?ctor:target));
        Assert.That(store.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
    }
}
