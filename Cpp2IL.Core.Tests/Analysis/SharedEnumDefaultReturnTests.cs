using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedEnumDefaultReturnTests
{
    [TestCase("exact", true)]
    [TestCase("duplicate", false)]
    [TestCase("missing-root", false)]
    [TestCase("no-concrete", false)]
    [TestCase("foreign-method", false)]
    [TestCase("open-alias", false)]
    [TestCase("reference-alias", false)]
    [TestCase("integer-not-enum", false)]
    [TestCase("nonzero", false)]
    [TestCase("class-type", false)]
    public void OnlyCompleteSameDefinitionEnumAliasesProveZeroDefault(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Shared", t.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            GenericParameterAttributes.NotNullableValueTypeConstraint, method);
        method.GenericParameters.Add(parameter); method.OverrideReturnType = parameter;
        var enumeration = app.Assemblies.SelectMany(a => a.Types).First(x => x.IsEnumType
            && ReferenceEquals(x.EnumUnderlyingType, t.SystemInt32Type));
        var zero = new Instruction(0, OpCode.Return, new Immediate(shape == "nonzero" ? 7 : 0));
        method.ControlFlowGraph = new([zero]);
        MethodAnalysisContext root = method;
        if (shape == "foreign-method")
        {
            var foreign = new InjectedMethodAnalysisContext(t.SystemObjectType, "Foreign", t.SystemObjectType,
                MethodAttributes.Public | MethodAttributes.Static, []);
            var other = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
                GenericParameterAttributes.None, foreign);
            foreign.GenericParameters.Add(other); foreign.OverrideReturnType = other; root = foreign;
        }
        TypeAnalysisContext closed = shape switch { "open-alias" => parameter, "reference-alias" => t.SystemStringType,
            "integer-not-enum" => t.SystemInt32Type, _ => enumeration };
        var concrete = new ConcreteGenericMethodAnalysisContext(root, [], [closed]);
        if (shape == "class-type") method.OverrideReturnType = new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, GenericParameterAttributes.None, method);
        var aliases = new List<MethodAnalysisContext> { method, concrete };
        if (shape == "duplicate") aliases.Add(concrete);
        if (shape == "missing-root") aliases.Remove(method);
        if (shape == "no-concrete") aliases.Remove(concrete);
        Assert.That(SharedEnumDefaultReturnRecovery.Rewrite(method, aliases), Is.EqualTo(expected ? 1 : 0));
        if (expected) Assert.That(((DefaultStructValue)zero.Operands[0]).Type, Is.SameAs(parameter));
        else Assert.That(zero.Operands[0], Is.TypeOf<Immediate>());
    }
}
