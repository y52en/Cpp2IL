using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64AtomicCompareExchangeTests
{
    private static (MethodAnalysisContext Method, Instruction Call, List<IOperand> Raw,
        LocalVariable Result, TypeAnalysisContext Element) Fixture(string typeName)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var element = app.SystemTypes.SystemObjectType.DeclaringAssembly.Types.Single(t => t.FullName == typeName);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "AtomicCaller",
            element, MethodAttributes.Public | MethodAttributes.Static, []);
        var raw = new List<IOperand> { new Immediate(0xACC538), new Register(null, "X0") };
        for (var i = 0; i < 16; i++) raw.Add(new Register(null, i < 8 ? "X" + i : "V" + (i - 8)));
        var call = new Instruction(0, OpCode.Call, raw) { NativeDirectCallTarget = 0xACC538 };
        Assert.That(call.MarkArm64DirectArgumentSnapshot(), Is.True);
        var result = new LocalVariable("result", new Register(null, "X0"));
        call.SetOperand(1, result);
        call.SetOperand(2, new LocalVariable("location", new Register(null, "X0"), new ByRefTypeAnalysisContext(element)));
        call.SetOperand(3, new LocalVariable("replacement", new Register(null, "X1"), element));
        call.SetOperand(4, new LocalVariable("expected", new Register(null, "X2"), element));
        caller.ControlFlowGraph = new([call, new(1, OpCode.Return, result)]);
        return (caller, call, raw, result, element);
    }

    [TestCase("System.String")]
    [TestCase("System.Int64")]
    [TestCase("System.IntPtr")]
    public void EmitsOneTypedAtomicCallWithExactLocationInputsAndOldValueResult(string typeName)
    {
        var f = Fixture(typeName);
        var inputs = f.Call.Operands.Skip(2).Take(3).ToArray();
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, true), Is.True);
        Assert.That(f.Call.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(f.Call.Operands.Count, Is.EqualTo(5));
        var target = (MethodAnalysisContext)f.Call.Operands[0];
        Assert.That(target.DeclaringType!.FullName, Is.EqualTo("System.Threading.Interlocked"));
        Assert.That(target.Name, Is.EqualTo("CompareExchange"));
        Assert.That(f.Call.Operands[1], Is.SameAs(f.Result));
        Assert.That(f.Result.Type, Is.SameAs(f.Element));
        Assert.That(f.Call.Operands.Skip(2).ToArray(), Is.EqualTo(inputs));
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, true), Is.False);
    }

    [Test]
    public void ReferenceComparandAndReplacementCanBeNull()
    {
        var f = Fixture("System.String");
        f.Call.SetOperand(3, new Immediate(0)); f.Call.SetOperand(4, new Immediate(0));
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, true), Is.True);
    }

    [TestCase("unproven-helper")]
    [TestCase("unknown-target")]
    [TestCase("virtual")]
    [TestCase("raw-pointer")]
    [TestCase("different-value-type")]
    [TestCase("different-comparand-type")]
    [TestCase("narrow-storage")]
    [TestCase("wrong-result-type")]
    [TestCase("bulk-replaced-slots")]
    [TestCase("externally-reordered-slots")]
    public void UnknownAbiTypesOrHelperNeverBecomeAtomicCalls(string shape)
    {
        var f = Fixture(shape == "narrow-storage" ? "System.Int32" : "System.String");
        var integer = TestGameLoader.LoadSimple2019Game().SystemTypes.SystemInt32Type;
        switch (shape)
        {
            case "unknown-target": f.Call.NativeDirectCallTarget = 0xACC580; break;
            case "virtual": f.Call.NativeVirtualDispatch = true; break;
            case "raw-pointer": f.Call.SetOperand(2, new Immediate(123)); break;
            case "different-value-type": f.Call.SetOperand(3, new LocalVariable("bad", new Register(null, "X1"), integer)); break;
            case "different-comparand-type": f.Call.SetOperand(4, new LocalVariable("bad", new Register(null, "X2"), integer)); break;
            case "wrong-result-type": f.Result.Type = integer; break;
            case "bulk-replaced-slots": f.Call.SetOperands(f.Call.Operands.ToList()); break;
            case "externally-reordered-slots": (f.Raw[3], f.Raw[4]) = (f.Raw[4], f.Raw[3]); break;
        }
        var original = f.Call.Operands.ToArray();
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, shape != "unproven-helper"), Is.False, shape);
        Assert.That(f.Call.Operands.ToArray(), Is.EqualTo(original));
        Assert.That(f.Call.Operands[0], Is.TypeOf<Immediate>());
    }

    [Test]
    public void CannotCertifyAnAlreadyReorderedRawRegisterList()
    {
        var f = Fixture("System.String");
        Assert.That(f.Call.MarkArm64DirectArgumentSnapshot(), Is.False);
        Assert.That(f.Call.HasArm64DirectArgumentSnapshot, Is.False);
    }
}
