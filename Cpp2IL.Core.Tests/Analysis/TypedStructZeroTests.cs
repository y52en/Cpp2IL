using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypedStructZeroTests
{
    [TestCase("full-store", true)]
    [TestCase("full-register", true)]
    [TestCase("partial-store", false)]
    [TestCase("partial-register", false)]
    [TestCase("unknown-width", false)]
    [TestCase("nonzero", false)]
    [TestCase("open", false)]
    [TestCase("primitive", false)]
    public void DefaultRequiresClosedLayoutAndEntireNativeZeroWidth(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var nullable = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Nullable`1");
        var type = new GenericInstanceTypeAnalysisContext(nullable,
            shape == "open" ? nullable.GenericParameters : [app.SystemTypes.SystemInt32Type]);
        var size = ClosedGenericValueLayout.TryGet(type, 8)?.Size ?? 8;
        var storage = new LocalVariable("storage", new(null, "stack_-16"),
            shape == "primitive" ? app.SystemTypes.SystemInt32Type : type);
        var zero = new Instruction(0, OpCode.Move, storage, new Immediate(shape == "nonzero" ? 1 : 0))
        {
            NativeWriteSize = shape == "full-store" ? (int)size : shape == "partial-store" ? 4 : 0,
            NativeZeroSize = shape == "full-register" ? (int)size : shape == "partial-register" ? 4 : 0
        };
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Default",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new([zero, new(1, OpCode.Return)]);
        Assert.That(TypedStructZeroRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        Assert.That(zero.Operands[1] is DefaultStructValue, Is.EqualTo(expected));
        if (expected) Assert.That(TypedStructZeroRecovery.Run(method), Is.Zero);
    }
}
