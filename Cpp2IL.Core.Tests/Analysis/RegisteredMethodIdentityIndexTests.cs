using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RegisteredMethodIdentityIndexTests
{
    [Test]
    public void BucketsHaveOnlyExactDefinitionAndCurrentRegisteredReferences()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=app.ConcreteGenericMethodsByRef.Values.First();
        var rows=RegisteredMethodIdentityIndex.Candidates(method);
        Assert.That(rows,Is.Not.Empty);
        Assert.That(rows.All(row=>ReferenceEquals(row.BaseMethodContext,method.BaseMethodContext)
            && app.ConcreteGenericMethodsByRef.TryGetValue(row.MethodRef!,out var live)&&ReferenceEquals(live,row)),Is.True);
        app.ConcreteGenericMethodsByRef.Remove(method.MethodRef!);
        Assert.That(RegisteredMethodIdentityIndex.Candidates(method).Contains(method),Is.False);
        app.ConcreteGenericMethodsByRef[method.MethodRef!]=method;
        Assert.That(RegisteredMethodIdentityIndex.Candidates(method).Contains(method),Is.True);
    }

    [Test]
    public void SameCountReplacementDoesNotAuthorizeAStaleRegisteredObject()
    {
        var app=TestGameLoader.LoadSimple2019Game();var prior=app.ConcreteGenericMethodsByRef.Values.First();
        Assert.That(RegisteredMethodIdentityIndex.Candidates(prior).Contains(prior),Is.True);
        var replacement=new ConcreteGenericMethodAnalysisContext(prior.MethodRef!,app);
        app.ConcreteGenericMethodsByRef[prior.MethodRef!]=replacement;
        var rows=RegisteredMethodIdentityIndex.Candidates(prior);
        Assert.That(rows.Contains(prior),Is.False);
        Assert.That(rows.Contains(replacement),Is.True);
    }

    [Test]
    public void VoidNoopsRequireRealRegisteredValueMethods()
    {
        var app=TestGameLoader.LoadSimple2019Game();var methods=app.ConcreteGenericMethodsByRef.Values.ToArray();
        var dispose=methods.First(m=>m.IsVoid&&!m.IsStatic&&m.Parameters.Count==0&&m.DeclaringType!.IsValueType);
        Assert.That(NativeRegisteredReceiverLeafProofs.VoidNoopMethod(dispose),Is.True);
        var synthetic=new ConcreteGenericMethodAnalysisContext(dispose.BaseMethodContext,dispose.TypeGenericParameters,dispose.MethodGenericParameters);
        Assert.That(NativeRegisteredReceiverLeafProofs.VoidNoopMethod(synthetic),Is.False);
        foreach(var method in methods.Where(m=>!m.IsVoid||m.IsStatic||m.Parameters.Count!=0||!m.DeclaringType!.IsValueType))
            Assert.That(NativeRegisteredReceiverLeafProofs.VoidNoopMethod(method),Is.False);
    }

    [TestCase("c0035fd6","c0035fd6",true)]
    [TestCase("c0035fd600000000","c0035fd6",false)]
    [TestCase("00008052c0035fd6","c0035fd6",false)]
    [TestCase("c0035fd6","c0035fd6c0035fd6",false)]
    public void NoopEvidenceMustCoverTheEntireReturnBody(string a,string b,bool expected)
        => Assert.That(NativeRegisteredReceiverLeafProofs.CompleteNoop(Convert.FromHexString(a),Convert.FromHexString(b)),Is.EqualTo(expected));
}
