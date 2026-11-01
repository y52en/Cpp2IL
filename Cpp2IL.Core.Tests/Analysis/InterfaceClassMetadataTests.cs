using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceClassMetadataTests
{
    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void ExactDirectOrCopiedMetadataNamesTheRepresentedInterface(bool generic, bool copied)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        TypeAnalysisContext type = app.Assemblies.SelectMany(a => a.Types)
            .Single(t => t.FullName == (generic ? "System.Collections.Generic.ICollection`1" : "System.IComparable"));
        if (generic) type = new GenericInstanceTypeAnalysisContext(type, [app.SystemTypes.SystemInt32Type]);
        var handle = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        var local = new LocalVariable("klass", new Register(null, "klass"));
        var copy = new LocalVariable("copy", new Register(null, "copy"));
        var defs = new Dictionary<LocalVariable, Instruction>
        {
            [local] = new(0, OpCode.Move, local, handle),
            [copy] = new(1, OpCode.Move, copy, local)
        };
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchInterface(copied ? copy : handle, defs), Is.SameAs(type));
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchInterface(type, defs), Is.SameAs(type));
    }

    [TestCase("type-hint")]
    [TestCase("memory")]
    [TestCase("arithmetic")]
    [TestCase("cycle")]
    [TestCase("non-interface")]
    [TestCase("nested-handle")]
    [TestCase("method-info")]
    public void UnprovenOrWrongRuntimeValuesCannotBecomeInterfaceKeys(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.IComparable");
        var handle = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        var local = new LocalVariable("klass", new Register(null, "klass"), handle);
        var defs = new Dictionary<LocalVariable, Instruction>();
        IOperand input = local;
        switch (shape)
        {
            case "memory": defs[local] = new(0, OpCode.Move, local, new MemoryOperand(local)); break;
            case "arithmetic": defs[local] = new(0, OpCode.Add, local, handle, new Immediate(0)); break;
            case "cycle": defs[local] = new(0, OpCode.Move, local, local); break;
            case "non-interface": input = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType, type.DeclaringAssembly); break;
            case "nested-handle": input = new RuntimeClassTypeAnalysisContext(handle, type.DeclaringAssembly); break;
            case "method-info": input = new RuntimeMethodInfoAnalysisContext(type.Methods.First(), type.DeclaringAssembly); break;
        }
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchInterface(input, defs), Is.Null);
    }
}
