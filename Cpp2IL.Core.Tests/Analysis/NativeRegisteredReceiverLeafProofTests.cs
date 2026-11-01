using System;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeRegisteredReceiverLeafProofTests
{
    [TestCase("001040b9c0035fd6","000040b9c0035fd6")]
    [TestCase("000c40f9c0035fd6","000440f9c0035fd6")]
    [TestCase("080442a9e00308aac0035fd6","080441a9e00308aac0035fd6")]
    public void CompleteBoxedUnboxedLoadEffectsMatch(string boxed,string unboxed)
        => Assert.That(NativeRegisteredReceiverLeafProofs.Equivalent(Convert.FromHexString(boxed),Convert.FromHexString(unboxed)),Is.True);

    [TestCase("001040b9c0035fd6","010040b9c0035fd6")]
    [TestCase("001040b9c0035fd6","000440b9c0035fd6")]
    [TestCase("001040b9c0035fd6","000040f9c0035fd6")]
    [TestCase("001040b9c0035fd6","000040b91f2003d5c0035fd6")]
    [TestCase("001040b9c0035fd6","000040b901000094c0035fd6")]
    [TestCase("001040b9c0035fd6","000040b9010000b9c0035fd6")]
    [TestCase("c0035fd6","c0035fd6")]
    public void OtherEffectsWidthsRegistersOrOffsetsDoNotMatch(string boxed,string unboxed)
        => Assert.That(NativeRegisteredReceiverLeafProofs.Equivalent(Convert.FromHexString(boxed),Convert.FromHexString(unboxed)),Is.False);

    [TestCase("001040b9010040b9c0035fd6")]
    [TestCase("e80300aa001040b9c0035fd6")]
    [TestCase("200040b9c0035fd6")]
    [TestCase("000440b8c0035fd6")]
    [TestCase("0804c1a9c0035fd6")]
    public void ReceiverEscapeOtherBasesAndWritebackAreRefused(string body)
        => Assert.That(NativeRegisteredReceiverLeafProofs.Normalize(Convert.FromHexString(body),16),Is.Null);
}
