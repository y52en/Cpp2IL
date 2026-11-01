using System;
using System.Linq;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeReceiverCounterpartProofTests
{
    private static readonly byte[] Boxed=Convert.FromHexString("f44fbea9fd7b01a9fd430091f40301aaf30300aa740a00f97f1a00b9740000b5e0031faac54afa97881e40b97f1200f9681e00b9fd7b41a9f44fc2a8c0035fd6");
    private static readonly byte[] Unboxed=Convert.FromHexString("f44fbea9fd7b01a9fd430091f40301aaf30300aa740200f97f0a00b9740000b5e0031faa59a4b597881e40b97f0a00f9680e00b9fd7b41a9f44fc2a8c0035fd6");
    private const ulong A=0xc1aaa8,B=0x1d44458;
    private static byte[] Words(params uint[] words)=>words.SelectMany(BitConverter.GetBytes).ToArray();

    [Test]
    public void CompleteConstructorPreservesEveryBranchAndThrowingCallee()
    {
        Assert.That(NativeReceiverCounterpartProof.Equivalent(Boxed,A,Unboxed,B,true),Is.True);
        var proof=NativeReceiverCounterpartProof.Normalize(Unboxed,B,0,true)!;
        Assert.That(proof,Has.Length.EqualTo(16));
        Assert.That(proof,Does.Contain(new NativeReceiverCounterpartProof.Effect(2,0x94000000,0xaad5e0)));
        Assert.That(proof.Count(p=>p.Kind==3),Is.EqualTo(4));
        Assert.That(NativeReceiverCounterpartProof.Equivalent(Boxed,A,Unboxed,B,false),Is.False);
    }

    [Test]
    public void All512OneBitModificationsAreRefused()
    {
        for(var at=0;at<Unboxed.Length;at++)for(var bit=0;bit<8;bit++)
        {
            var copy=Unboxed.ToArray();copy[at]^=(byte)(1<<bit);
            Assert.That(NativeReceiverCounterpartProof.Equivalent(Boxed,A,copy,B,true),Is.False,$"byte {at} bit {bit}");
        }
    }

    [TestCase(0x58000002u)]
    [TestCase(0x10000002u)]
    [TestCase(0x90000002u)]
    [TestCase(0xd61f0040u)]
    public void LiteralAddressAndIndirectBranchesAreNotPositionIndependent(uint instruction)
    {
        var left=Words(0xaa0003f3,instruction,0xf9000a61,0xd65f03c0);
        var right=Words(0xaa0003f3,instruction,0xf9000261,0xd65f03c0);
        Assert.That(NativeReceiverCounterpartProof.Equivalent(left,A,right,B,true),Is.False);
    }

    [Test]
    public void RawReceiverCannotEscapeIntoStackOrAnExternalCallee()
    {
        var left=Words(0xaa0003f3,0xf90003f3,0xf9000a61,0xd65f03c0);
        var right=Words(0xaa0003f3,0xf90003f3,0xf9000261,0xd65f03c0);
        Assert.That(NativeReceiverCounterpartProof.Equivalent(left,A,right,B,true),Is.False);
        var escaping=Unboxed.ToArray();BitConverter.GetBytes(0xaa1303e0u).CopyTo(escaping,32);
        Assert.That(NativeReceiverCounterpartProof.Equivalent(Boxed,A,escaping,B,true),Is.False);
    }

    [Test]
    public void AmbiguousReceiverAtJoinAndUnreachableTailAreRefused()
    {
        var code=Words(0xaa0003f3,0xb4000061,0xaa0303f3,0x14000002,0xaa0003f3,0xf9000a61,0xd65f03c0);
        Assert.That(NativeReceiverCounterpartProof.Normalize(code,A,16,true),Is.Null);
        Assert.That(NativeReceiverCounterpartProof.Normalize(Boxed.Concat(Words(0xd65f03c0)).ToArray(),A,16,true),Is.Null);
    }

    [Test]
    public void RejectsIncompleteOrNonReceiverBodies()
    {
        Assert.That(NativeReceiverCounterpartProof.Normalize(Boxed,A+1,16,true),Is.Null);
        Assert.That(NativeReceiverCounterpartProof.Normalize(Boxed.Take(63).ToArray(),A,16,true),Is.Null);
        Assert.That(NativeReceiverCounterpartProof.Normalize(Boxed,A,8,true),Is.Null);
        Assert.That(NativeReceiverCounterpartProof.Normalize(Words(0xd65f03c0),A,16,true),Is.Null);
    }
}
