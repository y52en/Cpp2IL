using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypedStructZeroRecoveryTests
{
    [TestCase("datetime",8,0,true)]
    [TestCase("datetime",4,0,false)]
    [TestCase("datetime",0,0,false)]
    [TestCase("datetime",0,8,true)]
    [TestCase("vector",0,12,true)]
    [TestCase("vector",8,0,false)]
    [TestCase("closed-generic",8,0,true)]
    [TestCase("open-definition",8,256,false)]
    [TestCase("scalar",4,0,false)]
    [TestCase("reference",8,0,false)]
    public void OnlyCompleteNativeZeroForKnownAggregateBecomesDefault(string kind,int width,int extent,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        TypeAnalysisContext Named(string name)=>app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName==name);
        var type=kind switch
        {
            "datetime"=>Named("System.DateTime"),"vector"=>Named("UnityEngine.Vector3"),
            "closed-generic"=>Named("System.Nullable`1").MakeGenericInstanceType([t.SystemInt32Type]),
            "open-definition"=>Named("System.Nullable`1"),"scalar"=>t.SystemInt32Type,_=>t.SystemStringType
        };
        var storage=new LocalVariable("storage",new Register(700,"stack_-40"),type);
        var store=new Instruction(0,OpCode.Move,storage,new Immediate(0)){NativeWriteSize=width,NativeZeroSize=extent};
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new ISILControlFlowGraph([store,new(1,OpCode.Return)])};
        Assert.That(TypedStructZeroRecovery.Run(method),Is.EqualTo(expected?1:0));
        Assert.That(store.Operands[1] is DefaultStructValue,Is.EqualTo(expected));
        Assert.That(TypedStructZeroRecovery.Run(method),Is.Zero);
    }

    [Test]
    public void LateCopyMaterializationUsesSameNativeProof()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var type=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.DateTime");
        var storage=new LocalVariable("storage",new Register(700,"stack_-40"),type);
        var zero=new LocalVariable("zero",new Register(0,"V0"));
        var store=new Instruction(1,OpCode.Move,storage,zero){NativeWriteSize=8};
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.Move,zero,new Immediate(0)),store,
                new(2,OpCode.CallVoid,new StringLiteral("observe"),new AddressOf(storage)),new(3,OpCode.Return)])};
        Assert.That(TypedStructZeroRecovery.Run(method),Is.Zero);
        SsaSimplifier.Run(method.ControlFlowGraph,[]);
        Assert.That(TypedStructZeroRecovery.Run(method),Is.EqualTo(1));
        Assert.That(store.Operands[1],Is.TypeOf<DefaultStructValue>());
    }
}
