using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DeferredGenericStorageTypingTests
{
    [TestCase(false,false)]
    [TestCase(true,false)]
    [TestCase(false,true)]
    [TestCase(true,true)]
    public void IncompleteReceiverDoesNotPreventLaterExactInstantiation(bool indirect,bool valueArgument)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var definition=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.Collections.Generic.List`1+Enumerator");
        var target=definition.Methods.Single(x=>x.Name=="MoveNext" && x.Parameters.Count==0);
        var argument=valueArgument?t.SystemInt32Type:t.SystemStringType;
        var concrete=new ConcreteGenericMethodAnalysisContext(target,[argument],[]);
        var storage=new LocalVariable("storage",new Register(700,"stack_-48"));
        var pointer=new LocalVariable("pointer",new Register(0,"X0"));
        var result=new LocalVariable("result",new Register(8,"X8"));
        var call=new Instruction(1,OpCode.Call,target,result,indirect?pointer:new AddressOf(storage));
        var caller=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
            {Locals=[storage,pointer,result],ParameterLocals=[],ControlFlowGraph=new ISILControlFlowGraph([
                new(0,OpCode.Move,pointer,new AddressOf(storage)),call,new(2,OpCode.Return)])};
        LocalVariables.ResolveTypesAndFields(caller);
        Assert.That(storage.Type,Is.Null,"a generic definition must not win before the actual receiver type resolves");
        Assert.That(result.Type,Is.SameAs(t.SystemBooleanType),"ordinary signature inference still runs");
        call.SetOperand(0,concrete);
        LocalVariables.ResolveTypesAndFields(caller);
        Assert.That(storage.Type,Is.SameAs(concrete.DeclaringType));
        Assert.That(storage.Type,Is.TypeOf<GenericInstanceTypeAnalysisContext>());
        Assert.That(((GenericInstanceTypeAnalysisContext)storage.Type!).GenericArguments.Single(),Is.SameAs(argument));
    }

    [Test]
    public void AlreadyKnownConcreteStorageIsNeverRetagged()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var definition=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.Collections.Generic.List`1+Enumerator");
        var target=definition.Methods.Single(x=>x.Name=="MoveNext" && x.Parameters.Count==0);
        var existing=definition.MakeGenericInstanceType([t.SystemStringType]);
        var other=new ConcreteGenericMethodAnalysisContext(target,[t.SystemInt32Type],[]);
        var storage=new LocalVariable("storage",new Register(700,"stack_-48"),existing);
        var caller=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.Call,other,
                new LocalVariable("result",new Register(0,"X0")),new AddressOf(storage)),new(1,OpCode.Return)])};
        Assert.That(LocalVariables.TypeAddressedLocals(caller),Is.False);
        Assert.That(storage.Type,Is.SameAs(existing));
    }
}
