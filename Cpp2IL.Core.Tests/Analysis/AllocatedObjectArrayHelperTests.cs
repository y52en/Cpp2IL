using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class AllocatedObjectArrayHelperTests
{
    [TestCase(1, true)]
    [TestCase(2, true)]
    [TestCase(3, true)]
    [TestCase(1, false)]
    [TestCase(2, false)]
    [TestCase(3, false)]
    public void ProvenNativeSignatureDropsOnlyPaddingAndRetainsActualArgumentsAndReturnSlot(int count, bool hasResult)
    {
        var operands = new System.Collections.Generic.List<IOperand> { new Immediate(123) };
        if (hasResult) operands.Add(new LocalVariable("result", new Register(null, "result")));
        var arguments = Enumerable.Range(1, count).Select(n => (IOperand)new Immediate(n)).ToArray();
        operands.AddRange(arguments); operands.Add(new Immediate(999));
        var call = new Instruction(0, hasResult ? OpCode.Call : OpCode.CallVoid, operands);
        var original = operands.ToArray();
        Assert.That(AllocatedObjectArrayHelperRecovery.TrimProvenPadding(call, count), Is.True);
        Assert.That(call.Operands, Is.EqualTo(original[..^1]));
        Assert.That(AllocatedObjectArrayHelperRecovery.TrimProvenPadding(call, count), Is.False);
        Assert.That(AllocatedObjectArrayHelperRecovery.TrimProvenPadding(call, 0), Is.False);
    }

    [TestCase(1, "fresh", true)]
    [TestCase(2, "fresh", true)]
    [TestCase(1, "alias", true)]
    [TestCase(2, "alias", true)]
    [TestCase(1, "null", true)]
    [TestCase(2, "null", true)]
    [TestCase(1, "incoming", false)]
    [TestCase(2, "incoming", false)]
    [TestCase(1, "string-array", false)]
    [TestCase(2, "string-array", false)]
    [TestCase(1, "primitive", false)]
    [TestCase(2, "primitive", false)]
    [TestCase(1, "unknown", false)]
    [TestCase(2, "unknown", false)]
    [TestCase(1, "live-result", false)]
    [TestCase(2, "live-result", false)]
    [TestCase(2, "wide-index", false)]
    [TestCase(2, "unbounded-index", false)]
    [TestCase(2, "multiply-defined", false)]
    [TestCase(1, "later-allocation", false)]
    [TestCase(2, "later-allocation", false)]
    [TestCase(1, "value-copy", true)]
    [TestCase(2, "value-copy", true)]
    [TestCase(2, "index-copy", true)]
    [TestCase(2, "index-or", true)]
    [TestCase(2, "arbitrary-or", false)]
    [TestCase(1, "value-cycle", false)]
    [TestCase(2, "value-cycle", false)]
    [TestCase(0, "fresh", false)]
    public void OnlyFreshExactObjectArrayAndManagedValuesQualify(int kind, string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = new SzArrayTypeAnalysisContext(shape == "string-array" ? t.SystemStringType : t.SystemObjectType);
        var root = new LocalVariable("root", new Register(null, "root"), type);
        var alias = new LocalVariable("alias", new Register(null, "alias"), type);
        var result = new LocalVariable("result", new Register(null, "result"));
        IOperand value = shape == "null" ? new Immediate(0) : new LocalVariable("value", new Register(null, "value"),
            shape == "primitive" ? t.SystemInt32Type : shape == "unknown" ? null : t.SystemStringType);
        IOperand index = shape == "wide-index" ? new LocalVariable("index", new Register(null, "index"), t.SystemInt64Type)
            : new Immediate(shape == "unbounded-index" ? long.MaxValue : 0);
        var allocation = shape == "incoming" ? new Instruction(0, OpCode.Nop)
            : new Instruction(0, OpCode.NewArr, root, type, new Immediate(1));
        var array = shape == "alias" ? alias : root;
        var call = kind == 1 ? new Instruction(2, OpCode.Call, new Immediate(123), result, array, value)
            : new Instruction(2, OpCode.Call, new Immediate(123), result, array, index, value);
        var instructions = new System.Collections.Generic.List<Instruction> { allocation };
        if (shape == "value-copy" || shape == "value-cycle")
        {
            var copy = new LocalVariable("valueCopy", new Register(null, "valueCopy"));
            instructions.Add(new(1, OpCode.Move, copy, shape == "value-cycle" ? copy : value));
            call.SetOperand(kind == 1 ? 3 : 4, copy);
        }
        if (shape == "index-copy")
        {
            var copy = new LocalVariable("indexCopy", new Register(null, "indexCopy"));
            instructions.Add(new(1, OpCode.Move, copy, index)); call.SetOperand(3, copy);
        }
        if (shape == "index-or" || shape == "arbitrary-or")
        {
            var copy = new LocalVariable("indexMaterialized", new Register(null, "indexMaterialized"));
            instructions.Add(new(1, OpCode.Or, copy, new Immediate(shape == "index-or" ? 0 : 1), new Immediate(2)));
            call.SetOperand(3, copy); index = new Immediate(2);
        }
        if (shape == "alias") instructions.Add(new(1, OpCode.Move, alias, root));
        if (shape == "multiply-defined") instructions.Add(new(1, OpCode.Move, root, new Immediate(0)));
        instructions.Add(call); instructions.Add(new(3, OpCode.Return, shape == "live-result" ? result : array));
        if (shape == "later-allocation") { instructions.Remove(allocation); instructions.Insert(instructions.IndexOf(call) + 1, allocation); }
        var cfg = new ISILControlFlowGraph(instructions);
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        Assert.That(AllocatedObjectArrayHelperRecovery.TryRewrite(cfg, call, definitions, kind), Is.EqualTo(expected));
        if (!expected) { Assert.That(call.OpCode, Is.EqualTo(OpCode.Call)); return; }
        if (kind == 1) Assert.That(call.OpCode, Is.EqualTo(OpCode.Nop));
        else
        {
            Assert.That(call.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(((ArrayAccess)call.Operands[0]).Array, Is.SameAs(array));
            Assert.That(((ArrayAccess)call.Operands[0]).Index, Is.EqualTo(index));
            Assert.That(call.Operands[1], Is.SameAs(value));
        }
    }

    [Test]
    public void BothCompleteHelperFingerprintsAreRequired()
    {
        var check = Convert.FromHexString("fd7bbfa9fd030091e10000b4080040f9e00301aa082140f9e10308aabd650194600000b4fd7bc1a8c0035fd6fb310194e1031faae2031faafd7bc1a8ca2c0114");
        var store = Convert.FromHexString("f50f1df8f44f01a9fd7b02a9fd830091f30300aa681a40b9f40301aaf50302aa9f02086ba30000546b300194e1031faae2031faabc2c0194680e148b151100f9fd7b42a9f44f41a9f50743f8c0035fd6");
        Assert.That(AllocatedObjectArrayHelperRecovery.ClassifyHelperBytes(check), Is.EqualTo(1));
        Assert.That(AllocatedObjectArrayHelperRecovery.ClassifyHelperBytes(store), Is.EqualTo(2));
        Assert.That(AllocatedObjectArrayHelperRecovery.ClassifyHelperBytes(store[..^4]), Is.Zero);
        check[^1] ^= 1; store[0] ^= 1;
        Assert.That(AllocatedObjectArrayHelperRecovery.ClassifyHelperBytes(check), Is.Zero);
        Assert.That(AllocatedObjectArrayHelperRecovery.ClassifyHelperBytes(store), Is.Zero);
    }

    [Test]
    public void EarlyAllocationRecoveryRetainsRealLengthAndProvesNonNull()
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes; var type = new SzArrayTypeAnalysisContext(t.SystemObjectType);
        var array = new LocalVariable("array", new Register(null, "array"));
        var discarded = new LocalVariable("discarded", new Register(null, "discarded"));
        var length = new Immediate(3);
        var typeCopy = new LocalVariable("typeCopy", new Register(null, "typeCopy"));
        var copy = new Instruction(-1, OpCode.Move, typeCopy, type);
        var allocation = new Instruction(0, OpCode.Call, new StringLiteral("il2cpp_vm_array_new_specific"), array, typeCopy, length, new Immediate(99));
        var guard = new Instruction(1, OpCode.Call, new Immediate(123), discarded, array);
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = new([copy, allocation, guard, new(2, OpCode.Return)]) };
        ArrayRecovery.RecoverAllocationsOnly(method);
        Assert.That(allocation.OpCode, Is.EqualTo(OpCode.NewArr));
        Assert.That(allocation.Operands[2], Is.EqualTo(length));
        Assert.That(ForwardNullCheckRecovery.FollowedBySameVirtualReceiver(method.ControlFlowGraph, guard), Is.True);
    }
}
