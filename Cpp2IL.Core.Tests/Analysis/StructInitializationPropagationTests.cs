using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StructInitializationPropagationTests
{
    [TestCase("ssa", false)]
    [TestCase("ssa", true)]
    [TestCase("post", false)]
    [TestCase("post", true)]
    public void ProvenStructReceiverOrReturnBufferCopyRemainsNativeAddress(string pass, bool hiddenReturn)
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "ByrefReceiver", types.SystemInt32Type.BaseType!, TypeAttributes.Public);
        var field = type.InjectFieldContext("x", types.SystemSingleType, FieldAttributes.Public);
        var source = new LocalVariable("storage", new Register(null, "storage"), type)
            {IsThis = !hiddenReturn, IsReturnBuffer = hiddenReturn};
        var alias = new LocalVariable("receiver", new Register(null, "receiver"), type);
        var use = new Instruction(2, OpCode.CallVoid, new StringLiteral("mutating receiver"), alias);
        var graph = new ISILControlFlowGraph(new List<Instruction> {
            new(0, OpCode.Move, new FieldReference(field, source, 0), new FloatLiteral(1f)),
            new(1, OpCode.Move, alias, source), use, new(3, OpCode.Return)});
        if (pass == "ssa") SsaSimplifier.Run(graph, [source]);
        else
        {
            var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
            method.ControlFlowGraph = graph; method.Locals = [source, alias]; method.ParameterLocals = [source];
            Simplifier.Simplify(method);
        }
        Assert.That(use.Operands.Last(), Is.SameAs(source));
    }

    [TestCase("ssa")]
    [TestCase("post")]
    public void TypedNativeAddressAliasStillForwardsAsAddress(string pass)
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "AddressedStruct", types.SystemInt32Type.BaseType!, TypeAttributes.Public);
        var storage = new LocalVariable("storage", new Register(null, "storage"), type);
        var alias = new LocalVariable("nativeReceiver", new Register(null, "nativeReceiver"), type);
        var address = new AddressOf(storage);
        var use = new Instruction(1, OpCode.CallVoid, new StringLiteral("mutating receiver"), alias);
        var graph = new ISILControlFlowGraph(new List<Instruction> {new(0, OpCode.Move, alias, address), use, new(2, OpCode.Return)});
        if (pass == "ssa") SsaSimplifier.Run(graph, []);
        else
        {
            var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
            method.ControlFlowGraph = graph; method.Locals = [storage, alias]; method.ParameterLocals = [];
            Simplifier.Simplify(method);
        }
        Assert.That(use.Operands.Last(), Is.SameAs(address), "native byref alias is not a managed value copy");
    }

    [TestCase("ssa", false)]
    [TestCase("ssa", true)]
    [TestCase("post", false)]
    [TestCase("post", true)]
    [TestCase("both", false)]
    [TestCase("both", true)]
    [TestCase("coalescer", false)]
    [TestCase("coalescer", true)]
    public void StructCopiesMustNotBecomeAliasesOfMutableStorage(string pass, bool mutateSource)
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "StructCopy", types.SystemInt32Type.BaseType!, TypeAttributes.Public);
        var field = type.InjectFieldContext("x", types.SystemSingleType, FieldAttributes.Public);
        var source = new LocalVariable("source", new Register(0, "source"), type);
        var copy = new LocalVariable("copy", new Register(pass == "coalescer" ? 0 : 1, "copy"), type);
        var capture = new Instruction(0, OpCode.Move, copy, source);
        var mutate = new Instruction(1, OpCode.Move, new FieldReference(field, mutateSource ? source : copy, 0), new FloatLiteral(17.5f));
        var first = new Instruction(2, OpCode.CallVoid, new StringLiteral("source"), source);
        var second = new Instruction(3, OpCode.CallVoid, new StringLiteral("copy"), copy);
        var graph = new ISILControlFlowGraph(new List<Instruction> {capture, mutate, first, second, new(4, OpCode.Return)});
        if (pass == "coalescer") CopyCoalescer.Run(graph);
        if (pass is "ssa" or "both") SsaSimplifier.Run(graph, [source]);
        if (pass is "post" or "both")
        {
            var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
            method.ControlFlowGraph = graph; method.Locals = [source, copy]; method.ParameterLocals = [source];
            Simplifier.Simplify(method);
        }
        Assert.That(first.Operands.Last(), Is.SameAs(source));
        Assert.That(second.Operands.Last(), Is.SameAs(copy), "value-type assignment captures a value, not an alias");
        Assert.That(capture.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((FieldReference)mutate.Operands[0]).Local, Is.SameAs(mutateSource ? source : copy));
    }

    [TestCase("ssa", "call")]
    [TestCase("ssa", "return")]
    [TestCase("post", "call")]
    [TestCase("post", "return")]
    [TestCase("both", "call")]
    [TestCase("both", "return")]
    public void InitializedStructUseRetainsItsPopulatedStorage(string pass, string use)
    {
        var types = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "PopulatedStruct", types.SystemInt32Type.BaseType!, TypeAttributes.Public);
        var field = type.InjectFieldContext("x", types.SystemSingleType, FieldAttributes.Public);
        var storage = new LocalVariable("hfa_arg", new Register(null, "hfa_arg"), type);
        var initialize = new Instruction(0, OpCode.Move, storage, new DefaultStructValue(type));
        var write = new Instruction(1, OpCode.Move, new FieldReference(field, storage, 0), new FloatLiteral(17.5f));
        var consume = use == "return" ? new Instruction(2, OpCode.Return, storage)
            : new Instruction(2, OpCode.CallVoid, new StringLiteral("consume"), storage);
        var graph = new ISILControlFlowGraph(new List<Instruction> { initialize, write, consume,
            new(3, OpCode.Return) });
        if (pass is "ssa" or "both") SsaSimplifier.Run(graph, []);
        if (pass is "post" or "both")
        {
            var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
            method.ControlFlowGraph = graph; method.Locals = [storage]; method.ParameterLocals = [];
            Simplifier.Simplify(method);
        }
        Assert.That(consume.Operands.Last(), Is.SameAs(storage),
            "default initializes mutable struct storage, not the value after field writes");
        Assert.That(initialize.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(write.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((FieldReference)write.Operands[0]).Local, Is.SameAs(storage));
    }
}
