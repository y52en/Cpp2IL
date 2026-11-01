using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ExplicitMethodInfoPhiTests
{
    [TestCase("valid", true)]
    [TestCase("move", true)]
    [TestCase("nested-copy", true)]
    [TestCase("generic-metadata", true)]
    [TestCase("generic-move", true)]
    [TestCase("generic-injected-base", false)]
    [TestCase("unmatched", false)]
    [TestCase("unrelated-merge", false)]
    [TestCase("nonzero", false)]
    [TestCase("raw-address", false)]
    [TestCase("ordinary-type", false)]
    [TestCase("injected-method", false)]
    [TestCase("memory", false)]
    [TestCase("unknown", false)]
    [TestCase("no-zero", false)]
    [TestCase("cycle", false)]
    [TestCase("ignored-raw", false)]
    public void OnlyMetadataBackedMethodInfoAndZeroInThisLookupMergeQualify(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=app.SystemTypes.SystemObjectType;
        var represented=owner.Methods.First(m=>m.Definition!=null);
        if(shape=="injected-method")represented=new InjectedMethodAnalysisContext(owner,"Injected",owner,MethodAttributes.Public|MethodAttributes.Static,[]);
        if(shape.StartsWith("generic-")) {
            var list=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
            represented=list.Methods.Single(m=>m.Definition!=null && m.Name=="get_Item");
            if(shape=="generic-injected-base")represented=new InjectedMethodAnalysisContext(list,"Injected",owner,MethodAttributes.Public,[]);
            represented=new ConcreteGenericMethodAnalysisContext(represented,[app.SystemTypes.SystemStringType],[]);
        }
        IOperand metadata=new RuntimeMethodInfoAnalysisContext(represented,owner.DeclaringAssembly!);
        if(shape=="raw-address")metadata=new Immediate(0x123456);
        if(shape=="ordinary-type")metadata=owner;
        LocalVariable Local(string name)=>new(name,new(null,name));
        var lookup=Local("lookup");var merged=Local("merged");var copied=Local("copied");var raw=Local("raw");var incoming=Local("incoming");
        if(shape=="memory")metadata=new MemoryOperand(raw);
        if(shape=="unknown")metadata=raw;
        var matched=new Instruction(-1,OpCode.Phi,lookup,new Immediate(0),new Immediate(1));
        var phi=new Instruction(-1,OpCode.Phi,merged,metadata,shape=="no-zero"?metadata:new Immediate(shape=="nonzero"?1:0));
        var home=new Block{ID=20};
        var definitions=new Dictionary<LocalVariable,Instruction>{[lookup]=matched,[merged]=phi};
        var homes=new Dictionary<Instruction,Block>{[matched]=home,[phi]=shape=="unrelated-merge"?new Block{ID=21}:home};
        if(shape is "move" or "generic-move") {definitions[incoming]=new(1,OpCode.Move,incoming,metadata);phi.SetOperand(1,incoming);}
        if(shape=="cycle")phi.SetOperand(2,merged);
        if(shape=="ignored-raw")phi.SetOperands(merged,metadata,new Immediate(0),raw);
        IOperand value=merged;
        if(shape=="nested-copy"){definitions[copied]=new(2,OpCode.Move,copied,merged);value=copied;}
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(value,definitions,homes,
            shape=="unmatched"?[]:[matched],shape=="ignored-raw"?local=>ReferenceEquals(local,raw):null),Is.EqualTo(expected));
    }
}
