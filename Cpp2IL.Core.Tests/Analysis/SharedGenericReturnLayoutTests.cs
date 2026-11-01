using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedGenericReturnLayoutTests
{
    [TestCase("reference-leaves",true)]
    [TestCase("same-size-integer-leaf",false)]
    [TestCase("different-nested-definition",false)]
    public void NestedGenericValuesRequireCompleteRecursiveStorageProof(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var types=app.Assemblies.SelectMany(a=>a.Types).ToArray();
        var list=types.Single(t=>t.FullName=="System.Collections.Generic.List`1");
        var pair=types.Single(t=>t.FullName=="System.Collections.Generic.KeyValuePair`2");
        var method=list.Methods.Single(m=>m.Name=="GetEnumerator" && m.ReturnType.IsValueType);
        var firstType=new GenericInstanceTypeAnalysisContext(pair,
            [app.SystemTypes.SystemObjectType,app.SystemTypes.SystemObjectType]);
        TypeAnalysisContext secondType=shape=="different-nested-definition"
            ?app.SystemTypes.SystemInt64Type
            :new GenericInstanceTypeAnalysisContext(pair,
                [app.SystemTypes.SystemStringType,shape=="same-size-integer-leaf"
                    ?app.SystemTypes.SystemInt64Type:app.SystemTypes.SystemStringType]);
        var first=new ConcreteGenericMethodAnalysisContext(method,[firstType],[]);
        var second=new ConcreteGenericMethodAnalysisContext(method,[secondType],[]);
        var firstSize=ClosedGenericValueLayout.TryGet(first.ReturnType,8);
        var secondSize=ClosedGenericValueLayout.TryGet(second.ReturnType,8);
        if(shape!="different-nested-definition")Assert.That(secondSize,Is.EqualTo(firstSize));
        var profile=SharedGenericReturnLayout.TryFromAliases(method,[method,first,second],8);
        Assert.That(profile!=null,Is.EqualTo(expected));
        Assert.That(TypeSizes.UnboxedSize(method.ReturnType,8),Is.Zero);
        if(profile!=null)Assert.That(profile.Size,Is.EqualTo(32));
    }

    [TestCase("valid",true)]
    [TestCase("other-definition",false)]
    [TestCase("missing-definition",false)]
    [TestCase("no-instantiation",false)]
    [TestCase("open-instantiation",false)]
    [TestCase("different-width",false)]
    [TestCase("same-width-different-kind",false)]
    [TestCase("duplicate",false)]
    [TestCase("pointer32",false)]
    public void AllAliasesMustProveTheSameMethodScopedClosedStorageWithoutChangingOpenTypes(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var list=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
        var method=list.Methods.Single(m=>m.Name=="GetEnumerator" && m.ReturnType.IsValueType);
        var first=new ConcreteGenericMethodAnalysisContext(method,[app.SystemTypes.SystemObjectType],[]);
        var argument=shape switch
        {
            "different-width"=>app.SystemTypes.SystemInt32Type,
            "same-width-different-kind"=>app.SystemTypes.SystemInt64Type,
            "open-instantiation"=>list.GenericParameters[0],
            _=>app.SystemTypes.SystemStringType
        };
        MethodAnalysisContext second=new ConcreteGenericMethodAnalysisContext(method,[argument],[]);
        if(shape=="other-definition")second=new ConcreteGenericMethodAnalysisContext(
            list.Methods.First(m=>m.Name!="GetEnumerator" && m.Parameters.Count==0),[app.SystemTypes.SystemObjectType],[]);
        MethodAnalysisContext[] aliases=shape switch
        {
            "missing-definition"=>[first,second],
            "no-instantiation"=>[method],
            "duplicate"=>[method,first,first],
            _=>[method,first,second]
        };
        var before=TypeSizes.UnboxedSize(method.ReturnType,8);
        var profile=SharedGenericReturnLayout.TryFromAliases(method,aliases,shape=="pointer32"?4:8);
        Assert.That(profile!=null,Is.EqualTo(expected));
        Assert.That(TypeSizes.UnboxedSize(method.ReturnType,8),Is.EqualTo(before));
        Assert.That(before,Is.Zero,"open T remains unknown outside the native method profile");
        if(profile!=null)
        {
            Assert.That(profile.Size,Is.EqualTo(24));
            Assert.That(profile.ConcreteAliases,Is.EqualTo(2));
            Assert.That(profile.Fields.Select(f=>f.Offset),Is.EqualTo(new long[]{0,8,12,16}));
            Assert.That(profile.Fields.Select(f=>f.Field.Name),Is.EqualTo(new[]{"list","index","version","current"}));
        }
    }
}
