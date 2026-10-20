using Cpp2IL.Core.InstructionSets;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64MoveKeepTests
{
    [Test]
    public void ActualCriAtomConstructorReplacesLowLaneInsteadOfOrCombining()
    {
        // Original RVA11c725c: MOVK X8,#0x10, after MOV X8,#0x800000008.
        var contract=NewArmV8InstructionSet.MoveKeepContract(0xf2800208u)!.Value;
        var result=(0x800000008UL & contract.KeepMask) | contract.Inserted;
        Assert.That(result,Is.EqualTo(0x800000010UL));
        Assert.That(result,Is.Not.EqualTo(0x800000018UL));
        Assert.That(contract.Destination,Is.EqualTo(Arm64Register.X8));
    }

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(3)]
    public void Every64BitLaneIsReplacedIncludingZeroImmediate(int lane)
    {
        foreach(var immediate in new uint[]{0,0x1234,0xffff})
        {
            var encoding=0xf2800000u | (uint)lane<<21 | immediate<<5 | 8u;
            var contract=NewArmV8InstructionSet.MoveKeepContract(encoding)!.Value;
            var mask=0xffffUL<<(lane*16);
            var original=0xfedcba9876543210UL;
            Assert.That((original & contract.KeepMask) | contract.Inserted,
                Is.EqualTo((original & ~mask) | (ulong)immediate<<(lane*16)));
            Assert.That(contract.Width,Is.EqualTo(8));
        }
    }

    [TestCase(0)]
    [TestCase(1)]
    public void WDestinationZeroExtendsUpper32BitsEvenForZeroLane(int lane)
    {
        var encoding=0x72800000u | (uint)lane<<21 | 8u;
        var contract=NewArmV8InstructionSet.MoveKeepContract(encoding)!.Value;
        var expected=0xffffffffUL & ~(0xffffUL<<(lane*16));
        Assert.That(ulong.MaxValue & contract.KeepMask | contract.Inserted,Is.EqualTo(expected));
        Assert.That(contract.Width,Is.EqualTo(4));
        Assert.That(contract.Destination,Is.EqualTo(Arm64Register.W8));
    }

    [TestCase(0xd2800208u)] // MOVZ, not MOVK
    [TestCase(0x12a00208u)] // MOVN, not MOVK
    [TestCase(0x72c00208u)] // invalid W destination with hw=2
    public void OtherOrInvalidEncodingsAreNotRelabeled(uint encoding)
    {
        Assert.That(NewArmV8InstructionSet.MoveKeepContract(encoding),Is.Null);
    }
}
