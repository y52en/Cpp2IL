using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class AbstractGenericVirtualSlotTests
{
    [TestCase("long")]
    [TestCase("single")]
    [TestCase("object")]
    [TestCase("open-argument")]
    [TestCase("derived")]
    [TestCase("malformed")]
    [TestCase("duplicate")]
    [TestCase("outside-slot")]
    public void AbstractSlotOnInflatedOwnerRetainsExactDefinitionAndArguments(string kind)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        // Actual stripped fixture metadata; choose an abstract generic class
        // slot whose VTable has no concrete implementation, as in the real
        // ExceptionHandler<T>.HandleException failure.
        var fixture=app.Assemblies.SelectMany(a=>a.Types)
            .Where(t=>!t.IsInterface && t.GenericParameters.Count==1 && t.Definition!=null)
            .SelectMany(t=>t.Methods.Where(m=>m.IsAbstract && !m.IsStatic && m.GenericParameters.Count==0
                && m.Definition!=null && m.Definition.slot<t.Definition!.VtableCount
                && app.ResolveContextForMethod(t.Definition.VTable[m.Definition.slot])==null)
                .Select(m=>(Owner:t,Method:m)))
            .OrderBy(x=>x.Method.FullName).First();
        var argument=kind switch {"long"=>types.SystemInt64Type,"single"=>types.SystemSingleType,
            "open-argument"=>fixture.Owner.GenericParameters[0],_=>types.SystemObjectType};
        var closed=new GenericInstanceTypeAnalysisContext(fixture.Owner,kind=="malformed"?[]:[argument]);
        Assert.That(closed.Methods,Is.Empty);
        TypeAnalysisContext receiver=kind=="derived"
            ?new InjectedTypeAnalysisContext(fixture.Owner.DeclaringAssembly,"Test","Child",closed,TypeAttributes.Public)
            :closed;
        var slot=kind=="outside-slot"?65535:fixture.Method.Definition!.slot;
        var originalMethodCount=fixture.Owner.Methods.Count;
        if(kind=="duplicate")fixture.Owner.Methods.Add(fixture.Method);
        MethodAnalysisContext? result;
        try{result=MetadataResolver.ResolveVTableSlot(app,receiver,slot);}
        finally{if(kind=="duplicate")fixture.Owner.Methods.RemoveAt(originalMethodCount);}
        // Injected child has no native vtable metadata. A generic base alone
        // cannot license inferring the child's dispatch slot or override.
        if(kind is "malformed" or "duplicate" or "outside-slot" or "derived")
        {Assert.That(result,Is.Null);return;}
        Assert.That(result,Is.TypeOf<ConcreteGenericMethodAnalysisContext>());
        var bound=(ConcreteGenericMethodAnalysisContext)result!;
        Assert.That(bound.BaseMethodContext,Is.SameAs(fixture.Method));
        var owner=(GenericInstanceTypeAnalysisContext)bound.DeclaringType!;
        Assert.That(owner.GenericType,Is.SameAs(fixture.Owner));
        Assert.That(owner.GenericArguments.Single(),Is.SameAs(argument));
        Assert.That(bound.IsAbstract,Is.True);
    }
}
