using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NamedExceptionCallTests
{
    [TestCase(true, true)]
    [TestCase(true, false)]
    [TestCase(false, true)]
    [TestCase(false, false)]
    public void ProvenNoreturnOverridesApparentRawResultUseButReturningFactoryKeepsItsValue(
        bool unconditionalRaiser, bool resultUsed)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var types = app.SystemTypes;
        var thrown = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.NullReferenceException");
        var result = new LocalVariable("rawX0", new Register(null, "X0"));
        var call = new Instruction(0, OpCode.Call, new Immediate(0x1000), result);
        var following = resultUsed
            ? new Instruction(1, OpCode.CallVoid, new StringLiteral("padding-consumer"), result)
            : new Instruction(1, OpCode.Return);
        var method = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([call, following]);
        MetadataResolver.RewriteNamedExceptionCall(method, call, thrown, unconditionalRaiser);
        Assert.That(call.OpCode, Is.EqualTo(!unconditionalRaiser && resultUsed ? OpCode.Newobj : OpCode.Throw));
        Assert.That(call.Operands.Last(), Is.SameAs(thrown));
        if (!unconditionalRaiser && resultUsed) Assert.That(call.Destination, Is.SameAs(result));
        else Assert.That(call.Destination, Is.Null);
    }
}
