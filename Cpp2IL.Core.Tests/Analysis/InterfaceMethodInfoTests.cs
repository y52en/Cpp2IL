using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceMethodInfoTests
{
    [Test]
    public void OnlyExactMatchedInvokeDataMetadataLoadIsEligible()
    {
        var pointer=new LocalVariable("pointer",new Register(null,"x0"));
        var loaded=new LocalVariable("loaded",new Register(null,"x1"));
        var phi=new Instruction(0,OpCode.Phi,pointer,new Immediate(0),new Immediate(1));
        var definitions=new System.Collections.Generic.Dictionary<LocalVariable,Instruction>
        {
            [pointer]=phi,[loaded]=new(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:8))
        };
        Assert.That(InterfaceDispatchRecovery.IsMatchedInvokeDataInfo(loaded,definitions,[phi]),Is.True);
        Assert.That(InterfaceDispatchRecovery.IsMatchedInvokeDataInfo(loaded,definitions,[]),Is.False);
        Assert.That(InterfaceDispatchRecovery.IsMatchedInvokeDataInfo(new Immediate(0),definitions,[phi]),Is.False);
        definitions[loaded]=new(1,OpCode.Move,loaded,new MemoryOperand(pointer,addend:0));
        Assert.That(InterfaceDispatchRecovery.IsMatchedInvokeDataInfo(loaded,definitions,[phi]),Is.False);
    }

    [TestCase(true)]
    [TestCase(false)]
    public void OnlyTrailingKnownManagedRuntimeArgumentIsRemoved(bool isStatic)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var target=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Known",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public | (isStatic ? MethodAttributes.Static : 0),
            [app.SystemTypes.SystemStringType]);
        var receiver=new LocalVariable("receiver",new Register(null,"x0"));
        var value=new LocalVariable("value",new Register(null,"x1"));
        var hidden=new LocalVariable("hidden",new Register(null,"x2"));
        var call=isStatic ? new Instruction(0,OpCode.CallVoid,target,value,hidden)
                          : new Instruction(0,OpCode.CallVoid,target,receiver,value,hidden);
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(call),Is.True);
        Assert.That(call.Operands[^1],Is.SameAs(value));
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(call),Is.False);
    }

    [Test]
    public void UnknownCallAndArbitraryExtraValueAreNeverTrimmed()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var target=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Known",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public | MethodAttributes.Static,[]);
        var unknown=new Instruction(0,OpCode.CallVoid,new Immediate(123),new Immediate(0));
        var nonzero=new Instruction(1,OpCode.CallVoid,target,new Immediate(7));
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(unknown),Is.False);
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(nonzero),Is.False);
    }

    [Test]
    public void GenericMethodKeepsItsRuntimeMetadata()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var target=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Generic",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public | MethodAttributes.Static,[]);
        target.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T",0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR,GenericParameterAttributes.None,target));
        var call=new Instruction(0,OpCode.CallVoid,target,new Immediate(0));
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(call),Is.False);
        Assert.That(call.Operands.Count,Is.EqualTo(2));
    }

    [Test]
    public void ReturnValueAndExplicitArgumentRemainUnchanged()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var target=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Known",
            app.SystemTypes.SystemStringType,MethodAttributes.Public | MethodAttributes.Static,
            [app.SystemTypes.SystemStringType]);
        var result=new LocalVariable("result",new Register(null,"x0"));
        var value=new LocalVariable("value",new Register(null,"x0"));
        var call=new Instruction(0,OpCode.Call,target,result,value,new Immediate(0));
        Assert.That(InterfaceDispatchRecovery.TrimIgnoredMethodInfo(call),Is.True);
        Assert.That(call.Operands[1],Is.SameAs(result));
        Assert.That(call.Operands[2],Is.SameAs(value));
    }
}
