using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class InheritedGenericFieldTests
{
    private static InjectedTypeAnalysisContext Type(ApplicationAnalysisContext app, string name, TypeAnalysisContext? parent)
        => new(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Test", name, parent, TypeAttributes.Public);

    private static GenericParameterTypeAnalysisContext Parameter(InjectedTypeAnalysisContext owner)
    {
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR, GenericParameterAttributes.None, owner);
        owner.GenericParameters.Add(parameter);
        return parameter;
    }

    [Test]
    public void MetadataConstructedInstancesKeepTheirBaseType()
    {
        var app = TestGameLoader.LoadSimple2022Game();
        var instances = app.Assemblies.SelectMany(a => a.Types).SelectMany(t => t.Fields)
            .Select(f => f.FieldType).OfType<GenericInstanceTypeAnalysisContext>()
            .Where(t => t.GenericType.BaseType != null).ToArray();
        Assert.That(instances, Is.Not.Empty);
        foreach (var instance in instances)
            Assert.That(instance.BaseType, Is.Not.Null, instance.FullName);
    }

    [Test]
    public void TwoGenericInheritanceLevelsSubstituteTheirOwnArguments()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var baseType = Type(app, "Base", app.SystemTypes.SystemObjectType);
        var baseParameter = Parameter(baseType);
        baseType.InjectFieldContext("Data", baseParameter, FieldAttributes.Public);
        var middle = Type(app, "Middle", null);
        var middleParameter = Parameter(middle);
        middle.BaseType = new GenericInstanceTypeAnalysisContext(baseType, [middleParameter]);
        var closed = new GenericInstanceTypeAnalysisContext(middle, [app.SystemTypes.SystemStringType]);
        var leaf = Type(app, "Leaf", closed);
        var inherited = GenericInstanceFieldLayout.FindInheritedFieldAtOffset(leaf, 16);
        Assert.That(inherited?.Name, Is.EqualTo("Data"));
        Assert.That(inherited?.FieldType, Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(inherited?.DeclaringType, Is.TypeOf<GenericInstanceTypeAnalysisContext>());
        Assert.That(((GenericInstanceTypeAnalysisContext)inherited!.DeclaringType).GenericType, Is.SameAs(baseType));
        var firstBase = closed.BaseType;
        Assert.That(closed.BaseType, Is.SameAs(firstBase), "resolved base context must be stable");
    }

    [Test]
    public void NonGenericBaseOffsetsDetermineInheritedGenericDataPosition()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var root = Type(app, "Root", app.SystemTypes.SystemObjectType);
        root.InjectFieldContext("Kind", app.SystemTypes.SystemInt32Type, FieldAttributes.Public).Offset = 16;
        root.InjectFieldContext("Mode", app.SystemTypes.SystemInt32Type, FieldAttributes.Public).Offset = 20;
        var generic = Type(app, "Wrapper", root);
        generic.InjectFieldContext("Data", Parameter(generic), FieldAttributes.Public);
        var closed = new GenericInstanceTypeAnalysisContext(generic, [app.SystemTypes.SystemStringType]);
        var leaf = Type(app, "Leaf", closed);
        var receiver = new LocalVariable("this", new Register(null, "X0"), leaf);
        var load = new Instruction(0, OpCode.Move, new LocalVariable("data", new Register(null, "X1")), new MemoryOperand(receiver, addend: 24)) { NativeReadSize = 8 };
        var method = new InjectedMethodAnalysisContext(leaf, "Read", app.SystemTypes.SystemStringType, MethodAttributes.Public, []);
        method.ControlFlowGraph = new([load, new(1, OpCode.Return)]);
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.True);
        Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
        var reference = (FieldReference)load.Operands[1];
        Assert.That(reference.Field.Name, Is.EqualTo("Data"));
        Assert.That(reference.Field.FieldType, Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(reference.Local, Is.SameAs(receiver));
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(leaf, 20)?.Name, Is.EqualTo("Mode"));
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(leaf, 25), Is.Null);
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(leaf, 24, 4), Is.Null, "partial pointer load is not a field read");
    }

    [TestCase("open")]
    [TestCase("struct")]
    [TestCase("overlap")]
    [TestCase("packing")]
    [TestCase("cycle")]
    public void UnsupportedLayoutsAreNotInferred(string reason)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var root = Type(app, "Root", app.SystemTypes.SystemObjectType);
        root.InjectFieldContext("Kind", app.SystemTypes.SystemInt32Type, FieldAttributes.Public).Offset = 16;
        var generic = Type(app, "Wrapper", root);
        var parameter = Parameter(generic);
        generic.InjectFieldContext("Data", parameter, FieldAttributes.Public);
        TypeAnalysisContext argument = app.SystemTypes.SystemStringType;
        if (reason == "open") argument = parameter;
        if (reason == "struct") argument = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Vector3");
        if (reason == "overlap") root.InjectFieldContext("Other", app.SystemTypes.SystemInt32Type, FieldAttributes.Public).Offset = 16;
        if (reason == "packing") generic.Attributes = TypeAttributes.Public | TypeAttributes.SequentialLayout;
        var closed = new GenericInstanceTypeAnalysisContext(generic, [argument]);
        var leaf = Type(app, "Leaf", closed);
        if (reason == "cycle") root.BaseType = leaf;
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(leaf, 24), Is.Null);
    }

    [Test]
    public void ClosedPrimitiveArgumentUsesItsOwnSizeRatherThanPointerSize()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var generic = Type(app, "PrimitiveWrapper", app.SystemTypes.SystemObjectType);
        generic.InjectFieldContext("Value", Parameter(generic), FieldAttributes.Public);
        generic.InjectFieldContext("Next", app.SystemTypes.SystemInt32Type, FieldAttributes.Public);
        var closed = new GenericInstanceTypeAnalysisContext(generic, [app.SystemTypes.SystemInt32Type]);
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(closed, 20)?.Name, Is.EqualTo("Next"));
        Assert.That(GenericInstanceFieldLayout.FindInheritedFieldAtOffset(closed, 24), Is.Null);
    }
}
