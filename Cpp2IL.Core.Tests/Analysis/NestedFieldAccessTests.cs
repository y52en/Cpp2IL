using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NestedFieldAccessTests
{
    [TestCase(16,4,"x",true)]
    [TestCase(20,4,"y",true)]
    [TestCase(24,4,"z",true)]
    [TestCase(16,12,"Vector",false)]
    [TestCase(16,2,null,false)]
    [TestCase(16,0,null,false)]
    [TestCase(27,4,null,false)]
    public void WidthDistinguishesWholeVectorFromNestedScalar(int offset,int width,string? expected,bool nested)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Holder",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("Vector",vector,FieldAttributes.Public);field.Offset=16;
        var root=new LocalVariable("holder",new Register(null,"X19"),owner);
        var result=NestedFieldAccess.Find(owner,root,offset,width);
        Assert.That(result?.Field.Name,Is.EqualTo(expected));
        Assert.That(result?.Parent!=null,Is.EqualTo(nested));
        if(result!=null) Assert.That(result.Local,Is.SameAs(root));
    }

    [Test]
    public void OverlappingAggregateMetadataIsRejected()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Overlap",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        owner.InjectFieldContext("A",vector,FieldAttributes.Public).Offset=16;
        owner.InjectFieldContext("B",vector,FieldAttributes.Public).Offset=16;
        Assert.That(NestedFieldAccess.Find(owner,new LocalVariable("root",new Register(null,"X19"),owner),16,4),Is.Null);
    }
}
