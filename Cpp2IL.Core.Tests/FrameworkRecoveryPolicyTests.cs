using Cpp2IL.Core.OutputFormats;

namespace Cpp2IL.Core.Tests;

public class FrameworkRecoveryPolicyTests
{
    [TestCase("mscorlib.dll", 1UL, false, true)]
    [TestCase("mscorlib.dll", 1UL, true, false)]
    [TestCase("mscorlib.dll", 0UL, true, true)]
    [TestCase("System.Core.dll", 1UL, true, false)]
    [TestCase("UnityEngine.CoreModule.dll", 1UL, true, false)]
    [TestCase("AWSSDK.Core.dll", 1UL, false, false)]
    [TestCase("Assembly-CSharp.dll", 1UL, false, false)]
    public void FrameworkRecovery_RequiresExplicitOptInAndNativeEntry(string assembly, ulong pointer, bool enabled, bool expectedSkip)
    {
        Assert.That(AsmResolverDllOutputFormatIlRecovery.SkipAssemblyRecovery(assembly, pointer, enabled), Is.EqualTo(expectedSkip));
    }
}
