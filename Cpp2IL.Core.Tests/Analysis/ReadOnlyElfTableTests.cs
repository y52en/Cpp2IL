using System.Collections.Generic;
using System.Reflection;
using System.Runtime.CompilerServices;
using LibCpp2IL.Elf;
using LibCpp2IL.PE;

namespace Cpp2IL.Core.Tests.Analysis;

public class ReadOnlyElfTableTests
{
    [TestCase("valid", true)]
    [TestCase("write", false)]
    [TestCase("no-read", false)]
    [TestCase("big-endian", false)]
    [TestCase("zero-fill", false)]
    [TestCase("overlap", false)]
    [TestCase("raw-truncated", false)]
    [TestCase("address-wrap", false)]
    public void RealTableReaderRequiresSingleReadOnlyFileBackedLittleEndianMapping(string shape, bool valid)
    {
        // Isolate the reader's actual mapping checks; no game or parsed metadata
        // is needed, and an uninitialized reader is never used for other actions.
        var elf = (ElfFile)RuntimeHelpers.GetUninitializedObject(typeof(ElfFile));
        void Set(string name, object value) => typeof(ElfFile).GetField(name, BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(elf, value);
        var entry = new ElfProgramHeaderEntry64 {
            _internalType = ElfProgramEntryType.PT_LOAD,
            _internalFlags = shape == "write" ? ElfProgramHeaderFlags.PF_R | ElfProgramHeaderFlags.PF_W
                : shape == "no-read" ? ElfProgramHeaderFlags.PF_X : ElfProgramHeaderFlags.PF_R,
            _internalVirtualAddr = 0x1000, _internalOffsetRaw = 0,
            _internalSizeRaw = shape == "zero-fill" ? 8UL : 64UL, _internalSizeVirtual = 64,
        };
        var entries = new List<IElfProgramHeaderEntry> { entry };
        if (shape == "overlap") entries.Add(entry);
        Set("_elfProgramHeaderEntries", entries);
        Set("_elfFileIdent", new ElfFileIdent { Endianness = shape == "big-endian" ? (byte)2 : (byte)1 });
        Set("_raw", shape == "raw-truncated" ? new byte[8] : new byte[64]);
        var result = elf.ReadOnlyMappedData(shape == "address-wrap" ? ulong.MaxValue - 4 : 0x1000, 40);
        Assert.That(result != null, Is.EqualTo(valid));
        if (valid) Assert.That(result!.Length, Is.EqualTo(40));
    }
}
