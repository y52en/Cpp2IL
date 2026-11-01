using System;
using System.Collections.Generic;
using System.Linq;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Tests.Analysis;

public class ElfEhFrameBoundsTests
{
    static byte[] Frame(bool personality = false, byte encoding = 0x1b,
        params (ulong Address, int Length)[] functions)
    {
        var bytes = new List<byte>();
        void Word(uint n) => bytes.AddRange(BitConverter.GetBytes(n));
        var payload = new List<byte> { 0, 0, 0, 0, 1, (byte)'z' };
        if (personality) payload.AddRange([(byte)'P', (byte)'L']);
        payload.AddRange([(byte)'R', 0, 1, 0x7c, 30]);
        if (personality) payload.AddRange([7, 0x9b, 0, 0, 0, 0, 0x1b, encoding]);
        else payload.AddRange([1, encoding]);
        Word((uint)payload.Count); bytes.AddRange(payload);
        foreach (var function in functions)
        {
            var at = bytes.Count;
            Word(13); Word((uint)(at + 4));
            Word(unchecked((uint)((long)function.Address - (0x2000L + at + 8))));
            Word((uint)function.Length); bytes.Add(0);
        }
        Word(0); return bytes.ToArray();
    }

    [TestCase(false, 0x1000UL)] [TestCase(true, 0x1000UL)]
    [TestCase(false, 0x3000UL)] [TestCase(true, 0x3000UL)]
    public void CompletePcRelativeSignedExtentSupportsBothCieAugmentations(bool personality, ulong address)
    {
        var bytes = Frame(personality, 0x1b, (address, 364));
        Assert.That(ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000), Is.EqualTo(new Dictionary<ulong, int> { [address] = 364 }));
    }

    [Test]
    public void FrameVirtualAddressIsDistinctFromItsFileOffset()
    {
        var frame = Frame(false, 0x1b, (0x1000, 364)); var file = new byte[frame.Length + 100]; frame.CopyTo(file, 44);
        Assert.That(ElfEhFrameBounds.Read(file, 44, frame.Length, 0x2000)[0x1000], Is.EqualTo(364));
    }

    [Test]
    public void AdjacentAndDisjointFunctionsRemainSeparate()
    {
        var bytes = Frame(false, 0x1b, (0x1000, 364), (0x116c, 16), (0x3000, 8));
        var bounds = ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000);
        Assert.That(bounds.Count, Is.EqualTo(3)); Assert.That(bounds[0x1000], Is.EqualTo(364));
    }

    [TestCase("truncated-record")] [TestCase("short-length")] [TestCase("extended-length")]
    [TestCase("missing-cie")] [TestCase("future-cie")] [TestCase("negative-size")]
    [TestCase("zero-size")] [TestCase("unaligned-size")] [TestCase("unaligned-address")]
    [TestCase("bad-augmentation-length")] [TestCase("nonzero-after-terminator")]
    public void MalformedFrameNeverReturnsPartialBounds(string shape)
    {
        var bytes = Frame(false, 0x1b, (0x1000, 364));
        var fde = checked((int)BitConverter.ToUInt32(bytes, 0)) + 4;
        void Word(int at, uint n) => BitConverter.GetBytes(n).CopyTo(bytes, at);
        if (shape == "truncated-record") bytes = bytes[..^6];
        if (shape == "short-length") Word(fde, 3);
        if (shape == "extended-length") Word(fde, uint.MaxValue);
        if (shape == "missing-cie") Word(fde + 4, 1);
        if (shape == "future-cie") Word(fde + 4, uint.MaxValue);
        if (shape == "negative-size") Word(fde + 12, uint.MaxValue);
        if (shape == "zero-size") Word(fde + 12, 0);
        if (shape == "unaligned-size") Word(fde + 12, 363);
        if (shape == "unaligned-address") Word(fde + 8, BitConverter.ToUInt32(bytes, fde + 8) + 1);
        if (shape == "bad-augmentation-length") bytes[fde + 16] = 1;
        if (shape == "nonzero-after-terminator") bytes = [.. bytes, 1];
        Assert.That(ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000), Is.Empty);
    }

    [TestCase(0x03)] [TestCase(0x1c)] [TestCase(0x9b)] [TestCase(0xff)]
    public void UnsupportedFdeEncodingsCannotBecomePcrelSignedWordBounds(byte encoding)
    {
        var bytes = Frame(false, encoding, (0x1000, 364));
        Assert.That(ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000), Is.Empty);
    }

    [TestCase("version")] [TestCase("augmentation")] [TestCase("missing-return-register")]
    [TestCase("duplicate-r")] [TestCase("bad-personality")]
    public void UnsupportedCieContractsAreSkipped(string shape)
    {
        var bytes = Frame(shape == "bad-personality", 0x1b, (0x1000, 364));
        if (shape == "version") bytes[8] = 3;
        if (shape == "augmentation") bytes[9] = (byte)'x';
        if (shape == "missing-return-register") bytes[15] = 0;
        if (shape == "duplicate-r") bytes[10] = (byte)'X';
        if (shape == "bad-personality") bytes[18] = 0x50;
        Assert.That(ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000), Is.Empty);
    }

    [TestCase(false)] [TestCase(true)]
    public void OverlappingOrDuplicateStartsAreNotProofs(bool duplicate)
    {
        var bytes = Frame(false, 0x1b, (0x1000, 364), (duplicate ? 0x1000UL : 0x1100UL, 16), (0x3000, 8));
        var bounds = ElfEhFrameBounds.Read(bytes, 0, bytes.Length, 0x2000);
        Assert.That(bounds.Count, Is.EqualTo(1)); Assert.That(bounds[0x3000], Is.EqualTo(8));
    }

    [TestCase(-1, 1)] [TestCase(0, -1)] [TestCase(0, 1000)] [TestCase(int.MaxValue, 1)]
    public void OutOfRangeSectionSpansAreRefused(int offset, int size)
        => Assert.That(ElfEhFrameBounds.Read(new byte[16], offset, size, 0x2000), Is.Empty);
}
