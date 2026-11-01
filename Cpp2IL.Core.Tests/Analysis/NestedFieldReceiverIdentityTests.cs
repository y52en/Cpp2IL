using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NestedFieldReceiverIdentityTests
{
    [TestCase("replace")] [TestCase("coalesce")] [TestCase("ssa")] [TestCase("simplify")]
    public void CopyReplacementUpdatesTheCompleteNestedReceiverPath(string pass)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","NestedOwner",t.SystemObjectType,TypeAttributes.Public);
        var outer=owner.InjectFieldContext("value",t.SystemInt32Type,FieldAttributes.Public);outer.Offset=24;
        var inner=owner.InjectFieldContext("component",t.SystemInt32Type,FieldAttributes.Public);inner.Offset=0;
        var source=new LocalVariable("source",new Register(3,"X3",1),owner);
        var copy=new LocalVariable("copy",new Register(3,"X3",2),owner);
        var parent=new FieldReference(outer,copy,24);
        var leaf=new FieldReference(inner,copy,0){Parent=parent};
        var result=new LocalVariable("result",new Register(0,"X0"),t.SystemInt32Type);
        var method=new InjectedMethodAnalysisContext(owner,"Read",t.SystemInt32Type,MethodAttributes.Public|MethodAttributes.Static,[])
        {
            ControlFlowGraph=new([new(0,OpCode.Move,copy,source),new(1,OpCode.Move,result,leaf),new(2,OpCode.Return,result)]),
            Locals=[source,copy,result],ParameterLocals=[]
        };
        if(pass=="replace")leaf.ReplaceLocal(copy,source);
        else if(pass=="coalesce")CopyCoalescer.Run(method);
        else if(pass=="ssa")SsaSimplifier.Run(method);
        else Simplifier.Simplify(method);
        Assert.That(parent.Local,Is.SameAs(leaf.Local));
        if(pass!="coalesce")Assert.That(leaf.Local,Is.SameAs(source));
    }

    [Test]
    public void ReplacementDoesNotInventAnAliasForADifferentParentReceiver()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var field=t.SystemInt32Type.Fields[0];
        var first=new LocalVariable("a",new Register(1,"X1"),t.SystemInt32Type);
        var other=new LocalVariable("b",new Register(2,"X2"),t.SystemInt32Type);
        var replacement=new LocalVariable("c",new Register(3,"X3"),t.SystemInt32Type);
        var parent=new FieldReference(field,other,0);
        var leaf=new FieldReference(field,first,0){Parent=parent};
        leaf.ReplaceLocal(first,replacement);
        Assert.That(leaf.Local,Is.SameAs(replacement));Assert.That(parent.Local,Is.SameAs(other));
        parent.Parent=leaf; // Malformed input must not hang the diagnostic pipeline.
        leaf.ReplaceLocal(replacement,first);
        Assert.That(leaf.Local,Is.SameAs(first));Assert.That(parent.Local,Is.SameAs(other));
    }
}
