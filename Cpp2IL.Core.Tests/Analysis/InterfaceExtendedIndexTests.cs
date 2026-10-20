using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceExtendedIndexTests
{
    [TestCase("truncate", true)]
    [TestCase("widen", true)]
    [TestCase("signed", false)]
    [TestCase("memory", false)]
    [TestCase("float", false)]
    [TestCase("call", false)]
    [TestCase("store", false)]
    public void OnlyExactPureIndexConversionsCanDisappearWithMatchedLookup(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var input = new LocalVariable("input", new Register(null, "input"));
        var output = new LocalVariable("output", new Register(null, "output"));
        IOperand source = shape == "memory" ? new MemoryOperand(input) : input;
        IOperand destination = shape == "store" ? new MemoryOperand(output) : output;
        var conversion = new Instruction(0, OpCode.NumericConvert, destination,
            shape switch { "truncate" => t.SystemUInt32Type, "signed" => t.SystemInt64Type,
                "float" => t.SystemDoubleType, _ => t.SystemUInt64Type }, t.SystemUInt32Type, source);
        if (shape == "call") conversion = new(0, OpCode.CallVoid, new StringLiteral("callback"), input);
        var slow = new Instruction(1, OpCode.Call, new Immediate(0xa7a4d0), output);
        var region = new HashSet<Block> { new() { Instructions = [conversion, slow] } };
        var result = typeof(InterfaceDispatchRecovery).GetMethod("RegionIsSideEffectFree", BindingFlags.NonPublic | BindingFlags.Static)!
            .Invoke(null, [region, slow]);
        Assert.That(result, Is.EqualTo(expected));
    }

    [TestCase("exact", true)]
    [TestCase("signed-widen", false)]
    [TestCase("wrong-narrow", false)]
    [TestCase("wrong-shift", false)]
    [TestCase("wrong-slot", false)]
    public void ExactUnsignedWordVtableIndexRetainsBothConversionContracts(string shape, bool match)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        LocalVariable L(string name) => new(name, new Register(null, name));
        var receiver = L("receiver"); var klass = L("klass"); var table = L("table");
        var offset = L("offset"); var sum = L("sum"); var narrow = L("narrow");
        var wide = L("wide"); var shifted = L("shifted"); var inner = L("inner"); var entry = L("entry");
        var defs = new Dictionary<LocalVariable, Instruction>
        {
            [klass] = new(0, OpCode.Move, klass, new MemoryOperand(receiver)),
            [offset] = new(1, OpCode.Move, offset, new MemoryOperand(table)),
            [sum] = new(2, OpCode.Add, sum, offset, new Immediate(shape == "wrong-slot" ? 17 : 16)),
            [narrow] = new(3, OpCode.NumericConvert, narrow,
                shape == "wrong-narrow" ? t.SystemInt32Type : t.SystemUInt32Type, t.SystemUInt32Type, sum),
            [wide] = new(4, OpCode.NumericConvert, wide,
                shape == "signed-widen" ? t.SystemInt64Type : t.SystemUInt64Type, t.SystemUInt32Type, narrow),
            [shifted] = new(5, OpCode.ShiftLeft, shifted, wide, new Immediate(shape == "wrong-shift" ? 3 : 4)),
            [inner] = new(6, OpCode.Add, inner, klass, shifted),
            [entry] = new(7, OpCode.Add, entry, inner, new Immediate(296))
        };
        var result = typeof(InterfaceDispatchRecovery).GetMethod("MatchVTableEntryChain", BindingFlags.NonPublic | BindingFlags.Static)!
            .Invoke(null, [defs, defs[entry], 16, 296L]);
        if (match) Assert.That(result, Is.SameAs(klass));
        else Assert.That(result, Is.Null);
    }
}
