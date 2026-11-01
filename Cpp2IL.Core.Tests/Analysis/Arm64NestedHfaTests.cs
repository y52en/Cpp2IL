using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64NestedHfaTests
{
    [TestCase("valid",false,true)]
    [TestCase("valid",true,true)]
    [TestCase("siblings",false,true)]
    [TestCase("nested-padding",false,false)]
    [TestCase("outer-padding",false,false)]
    [TestCase("nested-overlap",false,false)]
    [TestCase("outer-overlap",false,false)]
    [TestCase("mixed-float",false,false)]
    [TestCase("integer",false,false)]
    [TestCase("reference",false,false)]
    [TestCase("unknown-size",false,false)]
    [TestCase("recursive",false,false)]
    [TestCase("too-many",false,false)]
    public void NestedLanesRequireFullHomogeneousMetadataCoverage(string shape,bool wide,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var scalar=wide?t.SystemDoubleType:t.SystemSingleType;var width=wide?8:4;
        var assembly=t.SystemObjectType.DeclaringAssembly;
        var pair=new InjectedTypeAnalysisContext(assembly,"Test","Pair",t.SystemValueTypeType,TypeAttributes.Public|TypeAttributes.SequentialLayout);
        var wrapper=new InjectedTypeAnalysisContext(assembly,"Test","Wrapper",t.SystemValueTypeType,TypeAttributes.Public|TypeAttributes.SequentialLayout);
        var left=new InjectedFieldAnalysisContext("x",scalar,FieldAttributes.Public,pair,0);
        var right=new InjectedFieldAnalysisContext("y",scalar,FieldAttributes.Public,pair,width);
        pair.Fields.AddRange([left,right]);
        var root=new InjectedFieldAnalysisContext("value",pair,FieldAttributes.Public,wrapper,0);wrapper.Fields.Add(root);
        var sizes=new Dictionary<TypeAnalysisContext,long>{{pair,2*width},{wrapper,2*width}};
        if(shape=="siblings")
        {wrapper.Fields.Add(new InjectedFieldAnalysisContext("other",pair,FieldAttributes.Public,wrapper,2*width));sizes[wrapper]=4*width;}
        if(shape=="nested-padding")sizes[pair]+=width;
        if(shape=="outer-padding")sizes[wrapper]+=width;
        if(shape=="nested-overlap")right.OverrideOffset=0;
        if(shape=="outer-overlap")wrapper.Fields.Add(new InjectedFieldAnalysisContext("other",pair,FieldAttributes.Public,wrapper,0));
        if(shape=="mixed-float")right.OverrideFieldType=t.SystemDoubleType;
        if(shape=="integer")right.OverrideFieldType=t.SystemInt32Type;
        if(shape=="reference")right.OverrideFieldType=t.SystemStringType;
        if(shape=="unknown-size")sizes[pair]=0;
        if(shape=="recursive")right.OverrideFieldType=wrapper;
        if(shape=="too-many")
        {wrapper.Fields.Add(new InjectedFieldAnalysisContext("other",pair,FieldAttributes.Public,wrapper,2*width));
            wrapper.Fields.Add(new InjectedFieldAnalysisContext("last",scalar,FieldAttributes.Public,wrapper,4*width));sizes[wrapper]=5*width;}
        var actual=Arm64HfaLayout.Fields(wrapper,type=>sizes.GetValueOrDefault(type));
        Assert.That(actual!=null,Is.EqualTo(expected));
        if(actual==null)return;
        Assert.That(actual.Select(l=>l.Offset),Is.EqualTo(Enumerable.Range(0,shape=="siblings"?4:2).Select(n=>(long)n*width)));
        Assert.That(actual[0].Field,Is.SameAs(left));Assert.That(actual[1].Field,Is.SameAs(right));
        Assert.That(actual[0].Path,Is.EqualTo(new[]{root,left}));
        Assert.That(actual.All(l=>ReferenceEquals(l.FieldType,scalar)),Is.True);
        Assert.That(left.Offset,Is.Zero);Assert.That(root.Offset,Is.Zero);
    }
}
