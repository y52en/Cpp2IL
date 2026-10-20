using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericVirtualContextTests
{
    [Test]
    public void ClosedGenericBaseRetainsItsArgumentsWhenReceiverIsANongenericDerivedType()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var list=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.Collections.Generic.List`1");
        var closed=new GenericInstanceTypeAnalysisContext(list,[t.SystemInt64Type]);
        var child=new InjectedTypeAnalysisContext(list.DeclaringAssembly,"Test","Child",closed,TypeAttributes.Public);
        var getter=list.Methods.Single(m=>m.Name=="get_Item");
        var bound=MetadataResolver.BindVirtualContext(child,getter);
        Assert.That(bound,Is.Not.Null);
        Assert.That(bound!.ReturnType,Is.SameAs(t.SystemInt64Type));
        Assert.That(((GenericInstanceTypeAnalysisContext)bound.DeclaringType!).GenericType,Is.SameAs(list));
    }

    [Test]
    public void AGenericMethodNeedsItsOwnMethodArgumentsRatherThanAnUnboundMethodSpec()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var list=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.Collections.Generic.List`1");
        var closed=new GenericInstanceTypeAnalysisContext(list,[app.SystemTypes.SystemInt64Type]);
        // Stripped test metadata does not necessarily retain ConvertAll<U>.
        // Supply an explicit generic-method fixture on the exact real owner.
        var method=new InjectedMethodAnalysisContext(list,"GenericVirtual",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public,[]);
        method.GenericParameters.Add(new GenericParameterTypeAnalysisContext("U",0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR,GenericParameterAttributes.None,method));
        Assert.That(MetadataResolver.BindVirtualContext(closed,method),Is.Null);
    }

    [TestCase("unrelated",false)]
    [TestCase("malformed",false)]
    [TestCase("definition",true)]
    [TestCase("inherited-object",true)]
    public void GenericVirtualBindingNeverInventsOwnerArguments(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var list=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
        var target=shape=="inherited-object"?types.SystemObjectType.Methods.Single(m=>m.Name=="ToString" && m.Parameters.Count==0)
            :list.Methods.Single(m=>m.Name=="get_Item");
        TypeAnalysisContext receiver=shape switch
        {
            "unrelated"=>types.SystemStringType,"malformed"=>new GenericInstanceTypeAnalysisContext(list,[]),
            "definition"=>list,_=>new GenericInstanceTypeAnalysisContext(list,[types.SystemInt64Type])
        };
        var result=MetadataResolver.BindVirtualContext(receiver,target);
        Assert.That(result!=null,Is.EqualTo(expected));
        if(expected)Assert.That(result,Is.SameAs(target));
    }

    [TestCase("single",false)]
    [TestCase("long",false)]
    [TestCase("object",false)]
    [TestCase("long",true)]
    public void VirtualSlotKeepsTheMetadataReceiversConcreteTypeArguments(string kind,bool setter)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var types=app.SystemTypes;
        var list=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
        var declared=list.Methods.Single(m=>m.Name==(setter?"set_Item":"get_Item"));
        var argument=kind switch {"single"=>types.SystemSingleType,"long"=>types.SystemInt64Type,_=>types.SystemObjectType};
        var closed=new GenericInstanceTypeAnalysisContext(list,[argument]);
        var receiver=new LocalVariable("receiver",new(null,"X0"),closed);
        var klass=new LocalVariable("klass",new(null,"X9"),new RuntimeClassTypeAnalysisContext(closed,list.DeclaringAssembly));
        var result=new LocalVariable("result",new(null,"X0"));
        var layout=RuntimeMetadataLayout.For(new UnityVersion(2018,4,28,UnityVersionType.Final,1),8);
        var offset=layout.VTable+16L*declared.Definition!.slot;
        var call=new Instruction(0,OpCode.IndirectCall,new MemoryOperand(klass,addend:offset),result,receiver,
            new Immediate(0),setter?new Immediate(1):new MemoryOperand(klass,addend:offset+8),new Immediate(0));
        var caller=new InjectedMethodAnalysisContext(types.SystemObjectType,"Caller",types.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=new([call,new(1,OpCode.Return)])};
        caller.Locals=[klass,receiver,result];caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        Assert.That(MetadataResolver.ResolveVirtualCalls(caller,layout),Is.True);
        var bound=(MethodAnalysisContext)call.Operands[0];
        Assert.That(bound.DeclaringType,Is.TypeOf<GenericInstanceTypeAnalysisContext>());
        Assert.That(((GenericInstanceTypeAnalysisContext)bound.DeclaringType!).GenericType,Is.SameAs(list));
        Assert.That(setter?bound.Parameters[^1].ParameterType:bound.ReturnType,Is.SameAs(argument));
        Assert.That(call.NativeVirtualDispatch,Is.True);
    }
}
