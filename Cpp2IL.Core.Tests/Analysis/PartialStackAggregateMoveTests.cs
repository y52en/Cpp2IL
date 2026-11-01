using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PartialStackAggregateMoveTests
{
    [TestCase(0, true)]
    [TestCase(16, false)]
    [TestCase(40, true)]
    public void OnlyWholeWidthOrProvenLogicalCopiesTransmitAggregateType(int width, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.Dictionary`2+Enumerator");
        var type = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        var source = new LocalVariable("source", new Register(null,"stack_-C8")) { Type = type };
        var target = new LocalVariable("target", new Register(null,"V1"));
        var move = new Instruction(0, OpCode.Move, target, source) { NativeReadSize = width };
        var changed = (bool)typeof(LocalVariables).GetMethod("PropagateMove", BindingFlags.Static | BindingFlags.NonPublic)!
            .Invoke(null, new object[]{move,8})!;
        Assert.That(changed, Is.EqualTo(expected));
        Assert.That(target.Type == type, Is.EqualTo(expected));
    }

    [Test]
    public void PartialStoreCannotBackPropagateWholeDestinationTypeToVectorChunk()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.Collections.Generic.Dictionary`2+Enumerator");
        var type = new GenericInstanceTypeAnalysisContext(definition,
            [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType]);
        var source = new LocalVariable("source", new Register(null,"V1"));
        var target = new LocalVariable("target", new Register(null,"stack_-90")) { Type = type };
        var move = new Instruction(0, OpCode.Move, target, source) { NativeWriteSize = 16 };
        var changed = (bool)typeof(LocalVariables).GetMethod("PropagateMove", BindingFlags.Static | BindingFlags.NonPublic)!
            .Invoke(null, new object[]{move,8})!;
        Assert.That(changed, Is.False);
        Assert.That(source.Type, Is.Null);
    }
}
