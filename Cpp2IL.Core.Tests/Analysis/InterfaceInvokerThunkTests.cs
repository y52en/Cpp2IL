using System;
using System.Linq;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceInvokerThunkTests
{
    private const string CompleteHelper = "f30f1ef8fd7b01a9fd430091f30302aa690240f9e803002a2a3d42796a0100b42c5940f9eb031faa8c2100918d815ff8bf0101eb200100546b0500917f010aeb8c41009143ffff54e00313aae203082aa35a0094050000148a0140b94801080b2851288b00a10491020440a9fd7b41a9e00313aaf30742f840001fd6";

    [Test]
    public void CompleteOriginalFingerprintIsRequired()
    {
        var bytes = Convert.FromHexString(CompleteHelper);
        Assert.That(InterfaceInvokerThunkRecovery.MatchesHelperBytes(bytes), Is.True);
        Assert.That(InterfaceInvokerThunkRecovery.MatchesHelperBytes(bytes[..^4]), Is.False);
        bytes[^1] ^= 1;
        Assert.That(InterfaceInvokerThunkRecovery.MatchesHelperBytes(bytes), Is.False);
        bytes = Convert.FromHexString(CompleteHelper); bytes[0] ^= 1;
        Assert.That(InterfaceInvokerThunkRecovery.MatchesHelperBytes(bytes), Is.False);
    }

    [Test]
    public void SlotMustResolveExactlyToReferenceReturningZeroArgumentMember()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Collections.IEnumerable");
        var target = owner.Methods.Single(m => m.Name == "GetEnumerator");
        Assert.That(InterfaceInvokerThunkRecovery.Bind(owner, target.Definition!.slot), Is.SameAs(target));
        Assert.That(InterfaceInvokerThunkRecovery.Bind(owner, -1), Is.Null);
        Assert.That(InterfaceInvokerThunkRecovery.Bind(owner, 65536), Is.Null);
        Assert.That(InterfaceInvokerThunkRecovery.Bind(owner, 65535), Is.Null);
        Assert.That(InterfaceInvokerThunkRecovery.Bind(app.SystemTypes.SystemObjectType, 0), Is.Null);
    }

    [TestCase("System.IDisposable", "Dispose")]
    [TestCase("System.Collections.IEnumerator", "MoveNext")]
    [TestCase("System.Collections.IList", "Add")]
    public void VoidValueReturnOrExplicitArgumentsCannotUseThisProfile(string name, string member)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == name);
        var target = owner.Methods.Single(m => m.Name == member);
        Assert.That(InterfaceInvokerThunkRecovery.Bind(owner, target.Definition!.slot), Is.Null);
    }
}
