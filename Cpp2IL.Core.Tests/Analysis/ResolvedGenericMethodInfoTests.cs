using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ResolvedGenericMethodInfoTests
{
    [TestCase("string", true)]
    [TestCase("closed-reference", true)]
    [TestCase("value", false)]
    [TestCase("open", false)]
    [TestCase("pointer", false)]
    [TestCase("byref", false)]
    [TestCase("missing", false)]
    public void DefinitionEntryFallbackAcceptsOnlyCompleteReferenceSharing(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var list = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.Collections.Generic.List`1");
        TypeAnalysisContext argument = shape switch { "value" => t.SystemInt32Type, "open" => list.GenericParameters[0],
            "pointer" => new PointerTypeAnalysisContext(t.SystemInt32Type), "byref" => new ByRefTypeAnalysisContext(t.SystemStringType),
            "closed-reference" => new GenericInstanceTypeAnalysisContext(list, [t.SystemInt32Type]), _ => t.SystemStringType };
        var owner = new GenericInstanceTypeAnalysisContext(list, shape == "missing" ? [] : [argument]);
        Assert.That(MetadataResolver.ClosedReferenceOwnerArguments(owner), Is.EqualTo(expected));
    }

    [TestCase("valid", true)]
    [TestCase("metadata-local", true)]
    [TestCase("callvoid", true)]
    [TestCase("no-provenance", false)]
    [TestCase("wrong-native-entry", false)]
    [TestCase("different-definition", false)]
    [TestCase("open-metadata", false)]
    [TestCase("already-closed", false)]
    [TestCase("virtual", false)]
    [TestCase("missing-metadata", false)]
    [TestCase("misplaced-metadata", false)]
    [TestCase("extra-operand", false)]
    [TestCase("explicit-parameter", false)]
    [TestCase("generic-return", false)]
    [TestCase("method-generic", false)]
    public void ResolvedDefinitionNeedsExactHiddenMetadataNativeEntryAndUnchangedAbi(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var list = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.Collections.Generic.List`1");
        var returns = shape == "generic-return" ? list.GenericParameters[0] : shape == "callvoid" ? t.SystemVoidType : t.SystemBooleanType;
        var target = new InjectedMethodAnalysisContext(list, "KnownSize", returns, MethodAttributes.Public,
            shape == "explicit-parameter" ? [t.SystemInt32Type] : []);
        if (shape == "method-generic") target.GenericParameters.Add(new GenericParameterTypeAnalysisContext("U", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, GenericParameterAttributes.None, target));
        var concreteBase = shape == "different-definition"
            ? new InjectedMethodAnalysisContext(list, "KnownSize", returns, MethodAttributes.Public, []) : target;
        var concrete = new ConcreteGenericMethodAnalysisContext(concreteBase,
            shape == "open-metadata" ? list.GenericParameters : [t.SystemStringType], []);
        var metadata = new RuntimeMethodInfoAnalysisContext(concrete, list.DeclaringAssembly);
        var receiver = new LocalVariable("receiver", new(null, "X0"), concrete.DeclaringType);
        var result = new LocalVariable("result", new(null, "result"), returns);
        IOperand info = shape == "metadata-local"
            ? new LocalVariable("methodInfo", new(null, "X1"), metadata) : metadata;
        var call = shape == "callvoid" ? new Instruction(0, OpCode.CallVoid, target, receiver, info)
            : new Instruction(0, OpCode.Call, target, result, receiver, info);
        call.NativeDirectCallTarget = shape == "no-provenance" ? 0UL : 0x1000UL;
        call.NativeVirtualDispatch = shape == "virtual";
        if (shape == "already-closed") call.SetOperand(0, concrete);
        if (shape == "missing-metadata") call.SetOperand(call.Operands.Count - 1, new Immediate(0));
        if (shape == "misplaced-metadata") { call.SetOperand(call.Operands.Count - 2, info); call.SetOperand(call.Operands.Count - 1, receiver); }
        if (shape == "extra-operand") call.AddOperands([new Immediate(0)]);
        if (shape == "explicit-parameter") call.SetOperands(target, result, receiver, new Immediate(1), info);
        var caller = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var operands = call.Operands.ToArray();
        Assert.That(MetadataResolver.RefineResolvedGenericCall(caller, call,
            (_, entry) => shape != "wrong-native-entry" && entry == 0x1000), Is.EqualTo(expected));
        if (!expected) Assert.That(call.Operands.ToArray(), Is.EqualTo(operands));
        else
        {
            Assert.That(call.Operands[0], Is.SameAs(concrete));
            Assert.That(call.Operands.Skip(1), Is.EqualTo(operands.Skip(1)));
            Assert.That(MetadataResolver.RefineResolvedGenericCall(caller, call, (_, _) => true), Is.False);
        }
    }
}
