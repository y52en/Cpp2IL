using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class ResolvedRegisteredGenericCallTests
{
    [TestCase("registered", true)]
    [TestCase("missing-registry", false)]
    [TestCase("wrong-entry", false)]
    public void ResolvedMetadataOnlyContextNeedsExactRegisteredNativeInstance(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        ulong Entry(MethodAnalysisContext m)
        {
            var unboxed=app.InstructionSet.GetUnboxedMethodTarget(m);
            return unboxed!=0?unboxed:app.InstructionSet.GetPointerForMethod(m);
        }
        var target=app.ConcreteGenericMethodsByRef.Values.First(m=>!m.IsStatic
            &&m.Parameters.Count==0&&m.MethodGenericParameters.Count==0
            &&m.BaseMethodContext.GenericParameters.Count==0
            &&m.BaseMethodContext.DeclaringType!.GenericParameters.Count>0
            &&m.DeclaringType is GenericInstanceTypeAnalysisContext owner&&!owner.HasAnyGenericParameters()
            &&!m.ReturnType.HasAnyGenericParameters()
            &&TrivialConstructorRecovery.SameType(m.ReturnType,m.BaseMethodContext.ReturnType)
            &&TypeSizes.IsScalarValueType(m.ReturnType)&&Entry(m)!=0);
        var metadata=new ConcreteGenericMethodAnalysisContext(target.BaseMethodContext,
            target.TypeGenericParameters,target.MethodGenericParameters);
        Assert.That(metadata.UnderlyingPointer,Is.Zero);
        var entry=Entry(target);
        Assert.That(MetadataResolver.UnmappedNativeEntryMatches(metadata,entry),Is.True);
        var call=new Instruction(0,OpCode.Call,target.BaseMethodContext,
            new LocalVariable("result",new Register(null,"result"),metadata.ReturnType),
            new LocalVariable("receiver",new Register(null,"receiver"),metadata.DeclaringType),
            new RuntimeMethodInfoAnalysisContext(metadata,metadata.DeclaringType!.DeclaringAssembly))
            {NativeDirectCallTarget=shape=="wrong-entry"?0xA7A4D0UL:entry};
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var saved=app.ConcreteGenericMethodsByRef.Where(pair=>
            ReferenceEquals(pair.Value.BaseMethodContext,target.BaseMethodContext)).ToArray();
        if(shape=="missing-registry")foreach(var pair in saved)app.ConcreteGenericMethodsByRef.Remove(pair.Key);
        var operands=call.Operands.ToArray();
        try
        {
            Assert.That(MetadataResolver.RefineResolvedGenericCall(caller,call),Is.EqualTo(expected));
            if(expected)
            {
                Assert.That(call.Operands[0],Is.SameAs(metadata));
                Assert.That(call.Operands.Skip(1),Is.EqualTo(operands.Skip(1)),"existing ABI operands are preserved");
            }
            else Assert.That(call.Operands,Is.EqualTo(operands),"rejected refinement is atomic");
        }
        finally
        {
            if(shape=="missing-registry")foreach(var pair in saved)app.ConcreteGenericMethodsByRef[pair.Key]=pair.Value;
        }
    }
}
