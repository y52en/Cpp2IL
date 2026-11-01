using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClosedGenericValueSizeTests
{
    [TestCase("System.Collections.Generic.KeyValuePair`2", 16)]
    [TestCase("System.Collections.Generic.Dictionary`2+Enumerator", 40)]
    public void ClosedIntObjectSequentialValueHasNativeStorageSize(string name, int expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == name);
        var closed = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        Assert.That(TypeSizes.UnboxedSize(closed, 8), Is.EqualTo(expected));
    }

    [Test]
    public void OpenAndExplicitGenericLayoutsRemainUnknown()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        Assert.That(TypeSizes.UnboxedSize(definition, 8), Is.Zero);
        var closed = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        var previous = definition.OverrideAttributes;
        try
        {
            definition.OverrideAttributes = (definition.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.ExplicitLayout;
            Assert.That(TypeSizes.UnboxedSize(closed, 8), Is.Zero);
        }
        finally { definition.OverrideAttributes = previous; }
    }

    [Test]
    public void GenericFloatingAggregateIsNotMisclassifiedAsOrdinaryReturnStorage()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var closed = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemDoubleType]);
        Assert.That(ClosedGenericValueLayout.TryGet(closed, 8), Is.Null);
    }

    [Test]
    public void IncompleteArgumentsAndUnsupportedPointerProfileAreNotGuessed()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var incomplete = new GenericInstanceTypeAnalysisContext(definition, [app.SystemTypes.SystemInt32Type]);
        var closed = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        Assert.That(ClosedGenericValueLayout.TryGet(incomplete, 8), Is.Null);
        Assert.That(ClosedGenericValueLayout.TryGet(closed, 4), Is.Null);
    }

    [Test]
    public void ConcreteDateTimeNestedLayoutUsesExactMetadataOffsetsAndSize()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var all = app.Assemblies.SelectMany(a => a.Types).ToArray();
        var pair = all.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var date = all.Single(t => t.FullName == "System.DateTime");
        var closed = new GenericInstanceTypeAnalysisContext(pair, [date, app.SystemTypes.SystemObjectType]);
        Assert.That(TypeSizes.UnboxedSize(closed, 8), Is.EqualTo(16));
    }

    [Test]
    public void NestedClosedGenericAggregateKeepsTailPaddingAndAlignment()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var pair = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var inner = new GenericInstanceTypeAnalysisContext(pair,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        var outer = new GenericInstanceTypeAnalysisContext(pair, [inner, app.SystemTypes.SystemInt32Type]);
        Assert.That(TypeSizes.UnboxedSize(outer, 8), Is.EqualTo(24));
    }
}
