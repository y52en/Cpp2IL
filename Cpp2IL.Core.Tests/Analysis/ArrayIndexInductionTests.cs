using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayIndexInductionTests
{
    private static (InjectedMethodAnalysisContext, LocalVariable, LocalVariable) Loop(string shape = "valid")
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.SystemTypes.SystemObjectType;
        var array = new LocalVariable("array", new Register(null,"X19"), shape == "untyped-array" ? null : new SzArrayTypeAnalysisContext(owner));
        var seed = new LocalVariable("seed", new Register(null,"X21",0));
        var index = new LocalVariable("index", new Register(null,"X21",1));
        var next = new LocalVariable("next", new Register(null,"X21",2));
        var element = new LocalVariable("element", new Register(null,"X20"),owner);
        var condition = new LocalVariable("condition",new Register(null,"C"),app.SystemTypes.SystemBooleanType);
        var initialize = new Instruction(0,OpCode.Move,seed,new Immediate(shape == "negative-seed" ? -1 : 0));
        var phi = new Instruction(2,OpCode.Phi,index,seed,next);
        var update = new Instruction(4,OpCode.Add,next,index,new Immediate(1)) { NativeArithmeticSize = shape == "narrow" ? 4 : shape == "unknown-width" ? 0 : 8 };
        if (shape == "external") update.SetOperand(1,new LocalVariable("external",new Register(null,"X0")));
        if (shape == "pointer") seed.Type=owner;
        if (shape == "unknown-call") initialize.OpCode=OpCode.NotImplemented;
        var instructions = new List<Instruction> {
            initialize,new(1,OpCode.Jump,phi),phi,
            new(3,OpCode.Move,element,new ArrayAccess(array,index)),update,
            new(5,OpCode.CheckLess,condition,next,new Immediate(3)),
            new(6,OpCode.ConditionalJump,phi,condition),new(7,OpCode.Return),
        };
        if(shape == "duplicate-definition") instructions.Insert(1,new(8,OpCode.Move,seed,new Immediate(7)));
        var method=new InjectedMethodAnalysisContext(owner,"Loop",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new(instructions);
        method.Locals=[array,seed,index,next,element,condition];method.ParameterLocals=[];method.AnalysisWarnings=[];
        return (method,index,seed);
    }

    [Test]
    public void RealFixpointTypesClosedArrayCounterAndItsPhiAncestors()
    {
        var (method,index,seed)=Loop();
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(index.Type,Is.SameAs(method.AppContext.SystemTypes.SystemInt64Type));
        Assert.That(seed.Type,Is.SameAs(method.AppContext.SystemTypes.SystemInt64Type));
        Assert.That(ArrayIndexInductionRecovery.Run(method),Is.False);
    }

    [TestCase("negative-seed")]
    [TestCase("narrow")]
    [TestCase("unknown-width")]
    [TestCase("external")]
    [TestCase("pointer")]
    [TestCase("unknown-call")]
    [TestCase("untyped-array")]
    [TestCase("duplicate-definition")]
    public void UnknownOrIncompatibleCyclesAreNotTyped(string shape)
    {
        var (method,index,seed)=Loop(shape);
        Assert.That(ArrayIndexInductionRecovery.Run(method),Is.False);
        Assert.That(index.Type,Is.Null);
        Assert.That(seed.Type?.FullName,Is.EqualTo(shape=="pointer" ? "System.Object" : null));
    }
}
