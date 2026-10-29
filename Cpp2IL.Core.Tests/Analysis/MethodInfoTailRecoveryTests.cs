using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MethodInfoTailRecoveryTests
{
    [TestCase("same-vector", true)]
    [TestCase("nested-vector", true)]
    [TestCase("different-element", false)]
    [TestCase("same-name-impostor", false)]
    [TestCase("rank-one-array", false)]
    [TestCase("wrong-hidden-method", false)]
    public void TailReturnWrappersRequireExactMetadataAndHiddenMethod(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game(); app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;
        var element=app.SystemTypes.SystemStringType;
        TypeAnalysisContext targetReturn=new SzArrayTypeAnalysisContext(element);
        TypeAnalysisContext callerReturn=shape switch {
            "different-element"=>new SzArrayTypeAnalysisContext(owner),
            "same-name-impostor"=>new SzArrayTypeAnalysisContext(new InjectedTypeAnalysisContext(
                element.DeclaringAssembly,element.Namespace,element.Name,owner,TypeAttributes.Public)),
            "rank-one-array"=>new ArrayTypeAnalysisContext(element,1),
            _=>new SzArrayTypeAnalysisContext(element)
        };
        if(shape=="nested-vector") {
            callerReturn=new SzArrayTypeAnalysisContext(callerReturn);
            targetReturn=new SzArrayTypeAnalysisContext(targetReturn);
        }
        var target=new InjectedMethodAnalysisContext(owner,"ArrayTarget",targetReturn,MethodAttributes.Public,[]);
        var method=new InjectedMethodAnalysisContext(owner,"ArrayCaller",callerReturn,MethodAttributes.Public|MethodAttributes.Static,[]);
        var info=new RuntimeMethodInfoAnalysisContext(target,owner.DeclaringAssembly);
        var hidden=shape=="wrong-hidden-method"?new RuntimeMethodInfoAnalysisContext(
            new InjectedMethodAnalysisContext(owner,"Other",targetReturn,MethodAttributes.Public,[]),owner.DeclaringAssembly):info;
        var receiver=new LocalVariable("receiver",new Register(null,"X0"),owner);
        var jump=new Instruction(0,OpCode.IndirectJump,new MemoryOperand(info),receiver);
        var args=new List<IOperand>{receiver,hidden};
        args.AddRange(Enumerable.Range(2,6).Select(i=>(IOperand)new LocalVariable("arg"+i,new Register(null,"X"+i))));
        args.AddRange(Enumerable.Range(0,8).Select(i=>(IOperand)new LocalVariable("fp"+i,new Register(null,"V"+i))));
        jump.AddOperands(args);
        method.ControlFlowGraph=new([jump]);method.Locals=[receiver];method.ParameterLocals=[];method.AnalysisWarnings=[];
        Assert.That(MethodInfoTailRecovery.Recover(method),Is.EqualTo(expected));
        if(!expected) {
            Assert.That(jump.OpCode,Is.EqualTo(OpCode.IndirectJump));
            Assert.That(method.ControlFlowGraph.Instructions.Any(i=>i.OpCode==OpCode.Return),Is.False);
            return;
        }
        Assert.That(jump.Operands[0],Is.SameAs(target));
        Assert.That(jump.Destination,Is.Not.SameAs(receiver));
        Assert.That(method.ControlFlowGraph.Instructions.Single(i=>i.OpCode==OpCode.Return).Operands.Single(),Is.SameAs(jump.Destination));
        Assert.That(MethodInfoTailRecovery.Recover(method),Is.False);
    }

    [TestCase("reference", true)]
    [TestCase("integer", true)]
    [TestCase("void", true)]
    [TestCase("float", false)]
    [TestCase("void-used", false)]
    [TestCase("wrong-result-register", false)]
    [TestCase("generic-class", true)]
    [TestCase("generic-reference-flag", true)]
    [TestCase("generic-unconstrained", false)]
    [TestCase("generic-object", false)]
    [TestCase("generic-interface", false)]
    [TestCase("generic-value-flag", false)]
    [TestCase("generic-conflicting-flags", false)]
    public void OrdinaryDispatchPreservesExistingSsaResultAndContinuation(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game(); app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;
        var resultType=shape.StartsWith("void")?app.SystemTypes.SystemVoidType:shape=="float"?app.SystemTypes.SystemSingleType:
            shape=="integer"?app.SystemTypes.SystemInt32Type:app.SystemTypes.SystemStringType;
        var target=new InjectedMethodAnalysisContext(owner,"Target",resultType,MethodAttributes.Public,[]);
        if (shape.StartsWith("generic-"))
        {
            var attributes = shape == "generic-reference-flag" ? GenericParameterAttributes.ReferenceTypeConstraint
                : shape is "generic-value-flag" or "generic-conflicting-flags" ? GenericParameterAttributes.NotNullableValueTypeConstraint
                : GenericParameterAttributes.None;
            if (shape == "generic-conflicting-flags") attributes |= GenericParameterAttributes.ReferenceTypeConstraint;
            var generic = new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, attributes, target);
            if (shape == "generic-class") generic.ConstraintTypes.Add(app.SystemTypes.SystemStringType);
            if (shape == "generic-object") generic.ConstraintTypes.Add(owner);
            if (shape == "generic-interface") generic.ConstraintTypes.Add(new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Test", "Interface", owner, TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract));
            resultType = generic; target.ReturnType = generic;
        }
        var caller=new InjectedMethodAnalysisContext(owner,"Caller",app.SystemTypes.SystemInt32Type,MethodAttributes.Public|MethodAttributes.Static,[]);
        var info=new RuntimeMethodInfoAnalysisContext(target,owner.DeclaringAssembly);
        var receiver=new LocalVariable("this",new Register(null,"X0"),owner);
        var result=new LocalVariable("result",new Register(null,shape=="wrong-result-register"?"X3":"X0"));
        var call=new Instruction(0,OpCode.IndirectCall,new MemoryOperand(info),result);
        var args=new List<IOperand>{receiver,info};
        args.AddRange(Enumerable.Range(2,6).Select(i=>(IOperand)new LocalVariable("arg"+i,new Register(null,"X"+i))));
        args.AddRange(Enumerable.Range(0,8).Select(i=>(IOperand)new LocalVariable("fp"+i,new Register(null,"V"+i))));
        call.AddOperands(args);
        var ret=new Instruction(1,OpCode.Return,shape=="void-used"?result:new Immediate(0));
        caller.ControlFlowGraph=new([call,ret]);caller.Locals=new List<LocalVariable>{receiver,result};caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        Assert.That(MethodInfoTailRecovery.Recover(caller),Is.EqualTo(expected));
        Assert.That(caller.ControlFlowGraph.Instructions.Count(i=>i.OpCode==OpCode.Return),Is.EqualTo(1));
        Assert.That(caller.ControlFlowGraph.Instructions.Last(),Is.SameAs(ret));
        if(!expected){Assert.That(call.OpCode,Is.EqualTo(OpCode.IndirectCall));return;}
        Assert.That(call.OpCode,Is.EqualTo(target.IsVoid?OpCode.CallVoid:OpCode.Call));
        Assert.That(call.Operands[0],Is.SameAs(target));
        if(!target.IsVoid){Assert.That(call.Destination,Is.SameAs(result));Assert.That(result.Type,Is.SameAs(resultType));}
        Assert.That(MethodInfoTailRecovery.Recover(caller),Is.False);
    }

    [TestCase("valid", true)]
    [TestCase("offset", false)]
    [TestCase("hidden", false)]
    [TestCase("return", false)]
    [TestCase("short", false)]
    [TestCase("unknown", false)]
    [TestCase("duplicate", false)]
    public void ExactMethodPointerAndHiddenArgumentAreBothRequired(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); app.InstructionSet = new NewArmV8InstructionSet();
        var owner = app.SystemTypes.SystemObjectType;
        var target = owner.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0);
        var method = new InjectedMethodAnalysisContext(owner, "Tail",
            shape == "return" ? app.SystemTypes.SystemInt32Type : target.ReturnType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var info = new RuntimeMethodInfoAnalysisContext(target, owner.DeclaringAssembly);
        var infoLocal = new LocalVariable("info", new Register(null, "X1"), shape == "unknown" ? null : info);
        var pointer = new LocalVariable("pointer", new Register(null, "X2"));
        var receiver = new LocalVariable("receiver", new Register(null, "X0"), owner);
        var load = new Instruction(0, OpCode.Move, pointer, new MemoryOperand(infoLocal, addend: shape == "offset" ? 8 : 0));
        var jump = new Instruction(1, OpCode.IndirectJump, pointer, receiver);
        var args = new List<IOperand> { receiver, shape == "hidden" ? new Immediate(0) : info, pointer };
        args.AddRange(Enumerable.Range(3, 5).Select(i => (IOperand)new LocalVariable("arg" + i, new Register(null, "X" + i))));
        args.AddRange(Enumerable.Range(0, 8).Select(i => (IOperand)new LocalVariable("fp" + i, new Register(null, "V" + i))));
        if (shape == "short") args.RemoveAt(args.Count - 1);
        jump.AddOperands(args);
        var instructions = new List<Instruction> { load };
        if (shape == "duplicate") instructions.Add(new Instruction(2, OpCode.Move, pointer, new Immediate(0)));
        instructions.Add(jump);
        method.ControlFlowGraph = new(instructions);
        method.Locals = new List<LocalVariable> { pointer, receiver, infoLocal }; method.ParameterLocals = []; method.AnalysisWarnings = [];
        Assert.That(MethodInfoTailRecovery.Recover(method), Is.EqualTo(expected));
        if (!expected)
        {
            Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
            Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Return), Is.False);
            return;
        }
        Assert.That(jump.Operands[0], Is.SameAs(target));
        Assert.That(jump.Operands.Count, Is.EqualTo(4));
        Assert.That(jump.Destination, Is.Not.SameAs(receiver));
        Assert.That(method.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Return).Operands.Single(), Is.SameAs(jump.Destination));
        Assert.That(MethodInfoTailRecovery.Recover(method), Is.False);
    }
}
