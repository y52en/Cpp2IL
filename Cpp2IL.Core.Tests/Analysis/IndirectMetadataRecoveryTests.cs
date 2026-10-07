using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class IndirectMetadataRecoveryTests
{
    [Test]
    public void DoubleLoad_ResolvesOnlySecondDereference()
    {
        var pointer = new LocalVariable("pointer", new Register(null, "x8"));
        var slot = new MemoryOperand(addend: 0x1000);
        var definitions = new Dictionary<LocalVariable, Instruction> { [pointer] = new(0, OpCode.Move, pointer, slot) };
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), definitions,
            address => address == 0x1000 ? 0x2000UL : null), Is.EqualTo(0x2000UL));
        Assert.That(MetadataResolver.IndirectMetadataAddress(slot, definitions, _ => 0x2000UL), Is.Null);
    }

    [Test]
    public void MutableGlobalAndNonzeroOffsets_AreNotCollapsed()
    {
        var pointer = new LocalVariable("pointer", new Register(null, "x8"));
        var definitions = new Dictionary<LocalVariable, Instruction> { [pointer] = new(0, OpCode.Move, pointer, new MemoryOperand(addend: 0x1000)) };
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), definitions, _ => null), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer, addend: 8), definitions, _ => 0x2000UL), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer, pointer, scale: 8), definitions, _ => 0x2000UL), Is.Null);
        Assert.That(MetadataResolver.IndirectMetadataAddress(new MemoryOperand(pointer), new Dictionary<LocalVariable, Instruction>(), _ => 0x2000UL), Is.Null);
    }
}
