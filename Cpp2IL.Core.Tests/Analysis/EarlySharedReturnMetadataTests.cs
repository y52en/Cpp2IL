using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Utils;
using LibCpp2IL;

namespace Cpp2IL.Core.Tests.Analysis;

public class EarlySharedReturnMetadataTests
{
    [Test]
    public void MetadataUsageWithZeroPointerStillRequiresItsExactRegisteredNativeVariant()
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var target=app.ConcreteGenericMethodsByRef.Values.First(m=>!m.IsStatic&&m.Parameters.Count==0
            &&m.UnderlyingPointer!=0&&m.DeclaringType?.IsValueType==false&&!m.ReturnType.HasAnyGenericParameters()
            &&new Arm64CallingConventionResolver().ReturnsViaHiddenBuffer(m));
        // MetadataUsage.AsGenericMethodRef can create a new reference with the
        // same real MethodSpec but no populated code pointer. Leave the live
        // registered object and its own native pointer completely unchanged.
        var cloned=(Cpp2IlMethodRef)typeof(object).GetMethod("MemberwiseClone",BindingFlags.Instance|BindingFlags.NonPublic)!
            .Invoke(target.MethodRef,null)!;
        cloned.GenericVariantPtr=0;cloned.AdjustorThunkPtr=0;
        var info=new ConcreteGenericMethodAnalysisContext(cloned,app);
        Assert.That(info.UnderlyingPointer,Is.Zero);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(info,target.UnderlyingPointer),Is.True);
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"EarlySharedCaller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var block=new Block();block.Instructions.Add(new(0,OpCode.Move,new Register(null,"X1"),new MemoryOperand(addend:0x1234)));
        MethodAnalysisContext[] candidates=[target.BaseMethodContext,target];
        var selected=HiddenStructReturnRecovery.ExactZeroArgumentTarget(caller,block,1,target.UnderlyingPointer,candidates,_=>info,_=>null);
        Assert.That(selected,Is.SameAs(info));
        Assert.That(HiddenStructReturnRecovery.ExactZeroArgumentTarget(caller,block,1,target.UnderlyingPointer+4,candidates,_=>info,_=>null),Is.Null);
        var matching=RegisteredMethodIdentityIndex.Candidates(info).Where(m=>
            m.TypeGenericParameters.Count==info.TypeGenericParameters.Count
            &&m.MethodGenericParameters.Count==info.MethodGenericParameters.Count
            &&m.TypeGenericParameters.Zip(info.TypeGenericParameters,TrivialConstructorRecovery.SameType).All(equal=>equal)
            &&m.MethodGenericParameters.Zip(info.MethodGenericParameters,TrivialConstructorRecovery.SameType).All(equal=>equal)).ToArray();
        foreach(var method in matching)app.ConcreteGenericMethodsByRef.Remove(method.MethodRef!);
        try{Assert.That(HiddenStructReturnRecovery.ExactZeroArgumentTarget(caller,block,1,target.UnderlyingPointer,candidates,_=>info,_=>null),Is.Null);}
        finally{foreach(var method in matching)app.ConcreteGenericMethodsByRef[method.MethodRef!]=method;}
    }
}
