using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class UnmappedMethodInfoCallTests
{
    [TestCase("actual-entry",true)]
    [TestCase("foreign-helper",false)]
    [TestCase("different-entry",false)]
    [TestCase("zero-entry",false)]
    [TestCase("missing-info",false)]
    [TestCase("stale-other-info",false)]
    public void UnmappedDirectCallNeedsNativeIdentityAndItsOwnHiddenMetadata(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.First(m=>m.UnderlyingPointer!=0 && !m.IsStatic && m.Parameters.Count==0 && !m.IsVoid);
        var other=owner.Methods.First(m=>!ReferenceEquals(m,target));
        var entry=app.InstructionSet.GetUnboxedMethodTarget(target);
        if(entry==0)entry=app.InstructionSet.GetPointerForMethod(target);
        Assert.That(entry,Is.Not.Zero);
        var address=shape switch {"foreign-helper"=>0xA7A4D0UL,"different-entry"=>entry+4,"zero-entry"=>0UL,_=>entry};
        var receiver=new LocalVariable("receiver",new(null,"X0"),owner);
        var result=new LocalVariable("result",new(null,"X0-return"),target.ReturnType);
        List<IOperand> operands=[new Immediate((long)address),result,receiver,
            new RuntimeMethodInfoAnalysisContext(target,owner.DeclaringAssembly)];
        if(shape=="missing-info")operands.RemoveAt(3);
        if(shape=="stale-other-info")operands.Add(new RuntimeMethodInfoAnalysisContext(other,owner.DeclaringAssembly));
        var call=new Instruction(0,OpCode.Call,operands);
        var original=call.Operands.ToArray();
        var caller=new InjectedMethodAnalysisContext(owner,"Caller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=new ISILControlFlowGraph([call,new(1,OpCode.Return)])};
        app.MethodsByAddress.TryGetValue(address,out var prior);
        app.MethodsByAddress.Remove(address);
        try
        {
            var changed=MetadataResolver.ResolveCallsViaMethodInfo(caller);
            Assert.That(changed,Is.EqualTo(expected));
            if(expected)Assert.That(call.Operands[0],Is.SameAs(target));
            else Assert.That(call.Operands,Is.EqualTo(original));
        }
        finally{if(prior!=null)app.MethodsByAddress[address]=prior;}
    }

    [Test]
    public void MetadataOnlyGenericDelegateConstructorIsNotAHelperBody()
    {
        var app=TestGameLoader.LoadSimple2019Game();var owner=app.SystemTypes.SystemObjectType;
        var metadataOnly=new InjectedMethodAnalysisContext(owner,".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public,[]);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(metadataOnly,0xA7A4D0),Is.False);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(metadataOnly,0),Is.False);
    }

    [Test]
    public void SyntheticClosedMethodRequiresRegisteredSameDefinitionAndArguments()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var registered=app.ConcreteGenericMethodsByRef.Values.First(m=>m.TypeGenericParameters.Count>0
            && (app.InstructionSet.GetUnboxedMethodTarget(m)!=0||app.InstructionSet.GetPointerForMethod(m)!=0));
        var entry=app.InstructionSet.GetUnboxedMethodTarget(registered);
        if(entry==0)entry=app.InstructionSet.GetPointerForMethod(registered);
        var synthetic=new ConcreteGenericMethodAnalysisContext(registered.BaseMethodContext,
            registered.TypeGenericParameters,registered.MethodGenericParameters);
        Assert.That(synthetic.UnderlyingPointer,Is.Zero);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(synthetic,entry),Is.True);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(synthetic,0xA7A4D0),Is.False);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(synthetic,0),Is.False);
        var removed=app.ConcreteGenericMethodsByRef.Where(pair=>
            ReferenceEquals(pair.Value.BaseMethodContext,registered.BaseMethodContext)).ToArray();
        foreach(var pair in removed)app.ConcreteGenericMethodsByRef.Remove(pair.Key);
        try{Assert.That(MetadataResolver.UnmappedNativeEntryMatches(synthetic,entry),Is.False);}
        finally{foreach(var pair in removed)app.ConcreteGenericMethodsByRef[pair.Key]=pair.Value;}
    }

    [Test]
    public void SameDisplayNameIsNotRegisteredDefinitionIdentity()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var registered=app.ConcreteGenericMethodsByRef.Values.First(m=>m.TypeGenericParameters.Count>0
            && app.InstructionSet.GetPointerForMethod(m)!=0);
        var entry=app.InstructionSet.GetUnboxedMethodTarget(registered);
        if(entry==0)entry=app.InstructionSet.GetPointerForMethod(registered);
        var falseDefinition=new InjectedMethodAnalysisContext(registered.BaseMethodContext.DeclaringType!,
            registered.Name,registered.ReturnType,registered.Attributes,[]);
        var synthetic=new ConcreteGenericMethodAnalysisContext(falseDefinition,
            registered.TypeGenericParameters,registered.MethodGenericParameters);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(synthetic,entry),Is.False);
    }
}
