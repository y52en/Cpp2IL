using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstructorArrayIdentityTests
{
    [TestCase("same", true)]
    [TestCase("nested", true)]
    [TestCase("different-element", false)]
    [TestCase("same-name-impostor", false)]
    [TestCase("rank-one-array", false)]
    [TestCase("pointer", false)]
    [TestCase("null", false)]
    public void VectorIdentityUsesOnlyExactElementMetadata(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var element=app.SystemTypes.SystemStringType;
        TypeAnalysisContext left=new SzArrayTypeAnalysisContext(element);
        TypeAnalysisContext? right=shape switch {
            "different-element"=>new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType),
            "same-name-impostor"=>new SzArrayTypeAnalysisContext(new InjectedTypeAnalysisContext(
                element.DeclaringAssembly,element.Namespace,element.Name,app.SystemTypes.SystemObjectType,TypeAttributes.Public)),
            "rank-one-array"=>new ArrayTypeAnalysisContext(element,1),
            "pointer"=>new PointerTypeAnalysisContext(element),
            "null"=>null,
            _=>new SzArrayTypeAnalysisContext(element)
        };
        if(shape=="nested") {
            left=new SzArrayTypeAnalysisContext(left);
            right=new SzArrayTypeAnalysisContext(right!);
        }
        Assert.That(TrivialConstructorRecovery.SameType(left,right),Is.EqualTo(expected));
        Assert.That(TrivialConstructorRecovery.SameType(right,left),Is.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void GenericConstructorWithVectorArgumentStillRequiresExactDefinition(bool wrongElement)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var definition=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
        var left=definition.MakeGenericInstanceType([new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType)]);
        var right=definition.MakeGenericInstanceType([new SzArrayTypeAnalysisContext(
            wrongElement?app.SystemTypes.SystemObjectType:app.SystemTypes.SystemStringType)]);
        var constructor=new ConcreteGenericMethodAnalysisContext(
            definition.Methods.Single(m=>m.Name==".ctor"&&m.Parameters.Count==0),left.GenericArguments,[]);
        Assert.That(TrivialConstructorRecovery.SameType(left,right),Is.EqualTo(!wrongElement));
        Assert.That(TrivialConstructorRecovery.BindConstructorOwner(constructor,right),
            wrongElement?Is.Null:Is.SameAs(constructor));
    }
}
