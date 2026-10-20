using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstantFieldConstructorRecoveryTests
{
    private static (InjectedTypeAnalysisContext Type,MethodAnalysisContext Constructor,MethodAnalysisContext Base,
        FieldAnalysisContext Field,Instruction Store,Instruction BaseCall) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();var root=app.SystemTypes.SystemObjectType;
        var type=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","ConstantInitializers",root,TypeAttributes.Public);
        var field=type.InjectFieldContext("Count",app.SystemTypes.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
        var constructor=type.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public);
        var baseConstructor=root.Methods.First(m=>m.Name==".ctor" && m.Parameters.Count==0);
        baseConstructor.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(true));
        var self=new LocalVariable("this",new Register(null,"X0"),type){IsThis=true};
        constructor.ParameterLocals.Add(self);constructor.Locals.Add(self);
        var store=new Instruction(0,OpCode.Move,new FieldReference(field,self,16),new Immediate(8)){NativeWriteSize=4};
        var call=new Instruction(1,OpCode.CallVoid,baseConstructor,self);
        constructor.ControlFlowGraph=new([store,call,new(2,OpCode.Return)]);
        return(type,constructor,baseConstructor,field,store,call);
    }

    [TestCase("valid",true)]
    [TestCase("callback",false)]
    [TestCase("read",false)]
    [TestCase("wrong-width",false)]
    [TestCase("base-proof",false)]
    [TestCase("write-after-base",true)]
    public void OnlyCompleteNativeConstantWritesAndProvenBaseProduceTemplate(string shape,bool expected)
    {
        var f=Fixture();var block=f.Constructor.ControlFlowGraph!.Blocks.Single(b=>b.Instructions.Contains(f.Store));
        if(shape=="callback")block.Instructions.Insert(1,new(3,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="read")f.Store.SetOperand(1,new LocalVariable("unknown",new Register(null,"unknown")));
        if(shape=="wrong-width")f.Store.NativeWriteSize=8;
        if(shape=="base-proof")f.Base.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(false));
        if(shape=="write-after-base")f.Constructor.ControlFlowGraph=new([f.BaseCall,f.Store,new(2,OpCode.Return)]);
        Assert.That(ConstantFieldConstructorRecovery.Extract(f.Constructor)!=null,Is.EqualTo(expected));
    }

    [TestCase("valid",true)]
    [TestCase("wrong-value",false)]
    [TestCase("callback",false)]
    [TestCase("missing-store",false)]
    [TestCase("ambiguous",false)]
    [TestCase("extra-store",false)]
    [TestCase("wrong-class",false)]
    [TestCase("base-before-store",true)]
    [TestCase("base-before-store-wrong-order",false)]
    [TestCase("base-before-store-callback",false)]
    [TestCase("base-before-store-wrong-value",false)]
    public void FoldOnlyAnExactAllocationAdjacentInitializationWithoutPartialMutation(string shape,bool expected)
    {
        var f=Fixture();
        if(shape.StartsWith("base-before-store"))
            f.Constructor.ControlFlowGraph=new([f.BaseCall,f.Store,new(2,OpCode.Return)]);
        var template=ConstantFieldConstructorRecovery.Extract(f.Constructor);
        Assert.That(template,Is.Not.Null);
        f.Type.PutExtraData(ConstantFieldConstructorRecovery.CacheKey,shape=="ambiguous"?new[]{template,template}:new[]{template});
        var obj=new LocalVariable("object",new Register(null,"object"),f.Type);
        var allocation=new Instruction(0,OpCode.Newobj,obj,f.Type);
        if(shape=="wrong-class")allocation.SetOperand(1,new InjectedTypeAnalysisContext(f.Type.DeclaringAssembly,
            "Test","ConstantInitializers",f.Type.BaseType,TypeAttributes.Public));
        var store=new Instruction(1,OpCode.Move,new FieldReference(f.Field,obj,16),new Immediate(shape is "wrong-value" or "base-before-store-wrong-value"?9:8)){NativeWriteSize=4};
        var call=new Instruction(4,OpCode.CallVoid,f.Base,obj);
        var instructions=new System.Collections.Generic.List<Instruction>{allocation,store,call,new(5,OpCode.Return)};
        if(shape.StartsWith("base-before-store") && shape!="base-before-store-wrong-order")
            instructions=[allocation,call,store,instructions[^1]];
        if(shape=="base-before-store-callback")instructions.Insert(2,new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="callback")instructions.Insert(2,new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="missing-store")instructions.Remove(store);
        if(shape=="extra-store")instructions.Insert(2,new(2,OpCode.Move,new FieldReference(f.Field,obj,16),new Immediate(8)){NativeWriteSize=4});
        var caller=f.Type.InjectMethodContext("Caller",f.Constructor.ReturnType,MethodAttributes.Public|MethodAttributes.Static);
        caller.ControlFlowGraph=new(instructions);
        Assert.That(ConstantFieldConstructorRecovery.Run(caller),Is.EqualTo(expected?1:0));
        Assert.That(call.Operands[0],Is.SameAs(expected?f.Constructor:f.Base));
        Assert.That(store.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
    }

    [TestCase(0,"valid",true)]
    [TestCase(1,"valid",true)]
    [TestCase(2,"valid",true)]
    [TestCase(0,"wrong-order",false)]
    [TestCase(1,"wrong-order",false)]
    [TestCase(2,"wrong-order",false)]
    [TestCase(0,"callback",false)]
    [TestCase(1,"callback",false)]
    [TestCase(2,"callback",false)]
    public void BasePositionBetweenConstantStoresIsPartOfTheExactTemplate(int basePosition,string shape,bool expected)
    {
        var f=Fixture();var self=(LocalVariable)((FieldReference)f.Store.Operands[0]).Local;
        var second=f.Type.InjectFieldContext("Second",f.Field.FieldType,FieldAttributes.Public);second.Offset=20;
        var extra=new Instruction(3,OpCode.Move,new FieldReference(second,self,20),new Immediate(9)){NativeWriteSize=4};
        var native=new System.Collections.Generic.List<Instruction>{f.Store,extra};native.Insert(basePosition,f.BaseCall);
        native.Add(new(4,OpCode.Return));f.Constructor.ControlFlowGraph=new(native);
        var template=ConstantFieldConstructorRecovery.Extract(f.Constructor);
        Assert.That(template,Is.Not.Null);Assert.That(template!.BaseStoreIndex,Is.EqualTo(basePosition));
        f.Type.PutExtraData(ConstantFieldConstructorRecovery.CacheKey,new[]{template});
        var obj=new LocalVariable("obj",new(null,"obj"),f.Type);
        var one=new Instruction(5,OpCode.Move,new FieldReference(f.Field,obj,16),new Immediate(8)){NativeWriteSize=4};
        var two=new Instruction(6,OpCode.Move,new FieldReference(second,obj,20),new Immediate(9)){NativeWriteSize=4};
        var call=new Instruction(7,OpCode.CallVoid,f.Base,obj);
        var initialization=new System.Collections.Generic.List<Instruction>{one,two};
        initialization.Insert(shape=="wrong-order"?(basePosition+1)%3:basePosition,call);
        if(shape=="callback")initialization.Insert(1,new(8,OpCode.CallVoid,new StringLiteral("observable")));
        initialization.Insert(0,new(9,OpCode.Newobj,obj,f.Type));initialization.Add(new(10,OpCode.Return));
        var caller=f.Type.InjectMethodContext("MixedCaller",f.Constructor.ReturnType,MethodAttributes.Public|MethodAttributes.Static);
        caller.ControlFlowGraph=new(initialization);
        Assert.That(ConstantFieldConstructorRecovery.Run(caller),Is.EqualTo(expected?1:0));
        Assert.That(call.Operands[0],Is.SameAs(expected?f.Constructor:f.Base));
        Assert.That(one.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
        Assert.That(two.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.Move));
    }
}
