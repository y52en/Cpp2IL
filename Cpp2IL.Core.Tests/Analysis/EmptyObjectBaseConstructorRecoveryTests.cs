using System.Reflection;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class EmptyObjectBaseConstructorRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("alias", true)]
    [TestCase("missing-proof", false)]
    [TestCase("other-instance", false)]
    [TestCase("ordinary-method", false)]
    [TestCase("different-base", false)]
    [TestCase("multiple-calls", false)]
    public void OnlyProvenEmptyDirectObjectBaseOnThisIsRemoved(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var objectType = app.SystemTypes.SystemObjectType;
        var parent = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly,"Test","Parent",objectType,TypeAttributes.Public);
        var type = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly,"Test","Child",shape=="different-base"?parent:objectType,TypeAttributes.Public);
        var method = type.InjectMethodContext(shape=="ordinary-method"?"Work":".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public,[]);
        var self = new LocalVariable("this",new Register(null,"X0"),type) { IsThis=true };
        var target = objectType.Methods.First(m=>m.Name==".ctor" && m.Parameters.Count==0);
        target.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,new TrivialConstructorRecovery.ObjectProof(shape!="missing-proof"));
        var receiver = shape is "other-instance" or "alias" ? new LocalVariable("other",new Register(null,"X1"),type) : self;
        var store = new Instruction(0,OpCode.Move,new MemoryOperand(self,addend:16),new Immediate(42));
        var call = new Instruction(2,OpCode.CallVoid,target,receiver);
        var instructions = new List<Instruction> {store};
        if(shape=="alias")instructions.Add(new Instruction(1,OpCode.Move,receiver,self));
        instructions.Add(call);
        if(shape=="multiple-calls")instructions.Add(new Instruction(3,OpCode.CallVoid,target,self));
        instructions.Add(new Instruction(4,OpCode.Return));
        method.ControlFlowGraph=new(instructions);method.ParameterLocals=[self];method.Locals=[self,receiver];
        Assert.That(EmptyObjectBaseConstructorRecovery.Recover(method),Is.EqualTo(expected?1:0));
        Assert.That(call.OpCode,Is.EqualTo(expected?OpCode.Nop:OpCode.CallVoid));
        Assert.That(method.ControlFlowGraph.Instructions.Contains(store),Is.True);
        Assert.That(store.Operands[1].ToString(),Is.EqualTo("42"));
        Assert.That(EmptyObjectBaseConstructorRecovery.Recover(method),Is.Zero);
    }
}
