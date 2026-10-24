using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeNullableAccessorTests
{
    [TestCase(true)]
    [TestCase(false)]
    public void EveryByteOfTheCompleteGetterBodyMatters(bool hasValue)
    {
        var body = Convert.FromHexString(hasValue ? "00104039c0035fd6" : "000040b9c0035fd6");
        Assert.That(NativeNullableAccessorRecovery.MatchesBody(body, hasValue), Is.True);
        for (var at = 0; at < body.Length; at++)
        {
            var changed = (byte[])body.Clone(); changed[at] ^= 1;
            Assert.That(NativeNullableAccessorRecovery.MatchesBody(changed, hasValue), Is.False);
        }
        Assert.That(NativeNullableAccessorRecovery.MatchesBody(body, !hasValue), Is.False);
    }

    [TestCase("has-value", true)]
    [TestCase("get-default", true)]
    [TestCase("stale-info", true)]
    [TestCase("bad-body", false)]
    [TestCase("wrong-slot", false)]
    [TestCase("no-info", false)]
    [TestCase("object", false)]
    [TestCase("wide", false)]
    [TestCase("throwing-value", false)]
    [TestCase("virtual", false)]
    public void AccessorRequiresItsOwnHiddenMetadataByrefStorageAndNativeProof(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var assembly = types.SystemObjectType.DeclaringAssembly;
        var enumeration = new InjectedTypeAnalysisContext(assembly, "Test", "Result",
            assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public)
            { EnumUnderlyingType = shape == "wide" ? types.SystemInt64Type : types.SystemInt32Type };
        enumeration.Fields.Add(new InjectedFieldAnalysisContext("value__", enumeration.EnumUnderlyingType!, FieldAttributes.Public, enumeration));
        var nullable = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Nullable`1");
        var name = shape == "get-default" ? "GetValueOrDefault" : shape == "throwing-value" ? "get_Value" : "get_HasValue";
        var definition = nullable.Methods.Single(m => m.Name == name && m.Parameters.Count == 0);
        var target = new ConcreteGenericMethodAnalysisContext(definition, [enumeration], []);
        var slot = new LocalVariable("storage", new(null, "stack_-16"), shape == "object" ? types.SystemObjectType : target.DeclaringType);
        var result = new LocalVariable("result", new(null, "X0"));
        var info = new RuntimeMethodInfoAnalysisContext(target, assembly);
        var call = new Instruction(0, OpCode.Call, new Immediate(0x1000), result, new AddressOf(slot),
            shape == "no-info" ? new Immediate(0) : info);
        if (shape == "wrong-slot") call.SetOperands(new Immediate(0x1000), result, info, new AddressOf(slot));
        if (shape == "stale-info") call.AddOperands([new RuntimeMethodInfoAnalysisContext(definition, assembly)]);
        call.NativeVirtualDispatch = shape == "virtual";
        var caller = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        caller.ControlFlowGraph = new([call, new(1, OpCode.Return)]);
        var before = call.Operands.ToArray();
        Assert.That(NativeNullableAccessorRecovery.TryResolve(caller, call,
            (entry, isBoolean) => shape != "bad-body" && entry == 0x1000 && isBoolean == (shape != "get-default")), Is.EqualTo(expected));
        if (expected) { Assert.That(call.Operands[0], Is.SameAs(target)); Assert.That(call.Operands.Count, Is.EqualTo(4)); }
        else Assert.That(call.Operands.ToArray(), Is.EqualTo(before));
    }
}
