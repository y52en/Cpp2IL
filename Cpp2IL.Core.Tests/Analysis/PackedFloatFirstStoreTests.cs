using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedFloatFirstStoreTests
{
    [TestCase(0u, 0)]
    [TestCase(0x80000000u, -1)]
    [TestCase(0x3f000000u, 123)]
    [TestCase(0x00000001u, int.MinValue)]
    [TestCase(0x007fffffu, int.MaxValue)]
    public void CompleteFloatFirstWritePreservesBothLanes(uint lowBits, int highBits)
    {
        var bits = ((ulong)unchecked((uint)highBits) << 32) | lowBits;
        var (method, _) = Fixture(bits);
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method), Is.EqualTo(1));
        FloatLiteralRecovery.Run(method);
        var writes = method.ControlFlowGraph!.Instructions.Where(i => i.NativeWriteSize > 0).ToArray();
        Assert.That(writes.Length, Is.EqualTo(2));
        Assert.That(writes.All(i => i.NativeWriteSize == 4), Is.True);
        Assert.That(writes.Select(i => ((FieldReference)i.Operands[0]).Offset), Is.EqualTo(new[] { 0xb4, 0xb8 }));
        Assert.That(unchecked((uint)BitConverter.SingleToInt32Bits(((FloatLiteral)writes[0].Operands[1]).Value)), Is.EqualTo(lowBits));
        Assert.That(((Immediate)writes[1].Operands[1]).Value, Is.EqualTo(highBits));
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method), Is.Zero);
    }

    [TestCase(1)] [TestCase(2)] [TestCase(8)]
    public void ScalarLiteralConversionDoesNotTruncateUnprovedNativeWidth(int width)
    {
        var (method, store) = Fixture(0x123456783f800000UL);
        store.NativeWriteSize = width;
        var original = store.Operands[1];
        FloatLiteralRecovery.Run(method);
        Assert.That(store.Operands[1], Is.SameAs(original));
        Assert.That(((Immediate)store.Operands[1]).UnsignedValue, Is.EqualTo(0x123456783f800000UL));
    }

    [TestCase("gap")] [TestCase("overlap")] [TestCase("reference")]
    [TestCase("nan")] [TestCase("infinity")]
    public void IncompleteOrUnsupportedPartitionsRemainUnchanged(string shape)
    {
        var (method, store) = Fixture(shape == "nan" ? 0x123456787fc00001UL :
            shape == "infinity" ? 0x123456787f800000UL : 0x123456783f800000UL);
        var root = ((FieldReference)store.Operands[0]).Local.Type!;
        if (shape == "gap") root.Fields[1].Offset += 4;
        if (shape == "overlap") root.Fields[1].Offset -= 4;
        if (shape == "reference") root.Fields[1].FieldType = method.AppContext.SystemTypes.SystemObjectType;
        var operands = store.Operands.ToArray();
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method), Is.Zero);
        FloatLiteralRecovery.Run(method);
        Assert.That(store.Operands, Is.EqualTo(operands));
        Assert.That(method.ControlFlowGraph!.Instructions.Count(i => i.NativeWriteSize > 0), Is.EqualTo(1));
    }

    [TestCase(0)] [TestCase(4)]
    public void ScalarFloatWriteKeepsExistingConversion(int width)
    {
        var (method, store) = Fixture(0x3f800000);
        store.NativeWriteSize = width;
        FloatLiteralRecovery.Run(method);
        Assert.That(((FloatLiteral)store.Operands[1]).Value, Is.EqualTo(1f));
    }

    private static (InjectedMethodAnalysisContext, Instruction) Fixture(ulong bits)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var t = app.SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "PackedFloatFirst", t.SystemObjectType, TypeAttributes.Public);
        owner.InjectFieldContext("Barrier", t.SystemSingleType, FieldAttributes.Public).Offset = 0xb4;
        owner.InjectFieldContext("BarrierCount", t.SystemInt32Type, FieldAttributes.Public).Offset = 0xb8;
        var root = new LocalVariable("self", new Register(null, "X0"), owner);
        var store = new Instruction(0, OpCode.Move, new FieldReference(owner.Fields[0], root, 0xb4), new Immediate(unchecked((long)bits))) { NativeWriteSize = 8 };
        var method = new InjectedMethodAnalysisContext(owner, "Reset", t.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new(new System.Collections.Generic.List<Instruction> { store, new(1, OpCode.Return) }),
            Locals = [root], ParameterLocals = [root]
        };
        return (method, store);
    }
}
