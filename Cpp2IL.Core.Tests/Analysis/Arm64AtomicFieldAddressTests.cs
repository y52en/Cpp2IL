using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64AtomicFieldAddressTests
{
    private static (MethodAnalysisContext Method, Instruction Call, Instruction Add, Instruction? Copy,
        List<Instruction> Steps, LocalVariable Receiver, FieldAnalysisContext Field) Fixture(bool copy)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        Assert.That(field.BackingData, Is.Not.Null);
        Assert.That(field.FieldType.FullName, Is.EqualTo("System.IntPtr"));
        var caller = new InjectedMethodAnalysisContext(owner, "AtomicFieldCaller", field.FieldType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var receiver = new LocalVariable("receiver", new Register(null, "X19"), owner);
        var address = new LocalVariable("address", new Register(null, "X20"), app.SystemTypes.SystemUInt64Type);
        var add = new Instruction(0, OpCode.Add, address, receiver, new Immediate(field.Offset)) { NativeArithmeticSize = 8 };
        var steps = new List<Instruction> { add };
        Instruction? copied = null;
        if (copy)
        {
            var next = new LocalVariable("addressCopy", new Register(null, "X0"), app.SystemTypes.SystemUInt64Type);
            copied = new(1, OpCode.Move, next, address) { NativeRegisterCopySize = 8 };
            steps.Add(copied); address = next;
        }
        var raw = new List<IOperand> { new Immediate(0xACC55C), new Register(null, "X0") };
        for (var i = 0; i < 16; i++) raw.Add(new Register(null, i < 8 ? "X" + i : "V" + (i - 8)));
        var call = new Instruction(2, OpCode.Call, raw) { NativeDirectCallTarget = 0xACC55C };
        Assert.That(call.MarkArm64DirectArgumentSnapshot(), Is.True);
        var result = new LocalVariable("result", new Register(null, "X0"), field.FieldType);
        call.SetOperand(1, result); call.SetOperand(2, address);
        call.SetOperand(3, new LocalVariable("replacement", new Register(null, "X1"), field.FieldType));
        call.SetOperand(4, new LocalVariable("expected", new Register(null, "X2"), field.FieldType));
        steps.Add(call); steps.Add(new(3, OpCode.Return, result));
        caller.ControlFlowGraph = new(steps);
        return (caller, call, add, copied, steps, receiver, field);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void MetadataProvenFieldAddressBecomesAnExactManagedRef(bool copy)
    {
        var f = Fixture(copy);
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, true), Is.True);
        Assert.That(f.Call.Operands[2], Is.TypeOf<AddressOf>());
        var field = (FieldReference)((AddressOf)f.Call.Operands[2]).Target;
        Assert.That(field.Field, Is.SameAs(f.Field));
        Assert.That(field.Local, Is.SameAs(f.Receiver));
        Assert.That(field.Offset, Is.EqualTo(f.Field.DefaultOffset));
        Assert.That(f.Add.OpCode, Is.EqualTo(OpCode.Add)); // Recovery itself preserves other address consumers.
    }

    [TestCase("unknown-width")]
    [TestCase("narrow-width")]
    [TestCase("interior-offset")]
    [TestCase("unknown-offset")]
    [TestCase("wrong-receiver")]
    [TestCase("non-dominating")]
    [TestCase("duplicate-definition")]
    [TestCase("copy-width")]
    [TestCase("missing-metadata")]
    public void UnprovenPointerExpressionsKeepTheirDiagnosticCall(string shape)
    {
        var f = Fixture(shape == "copy-width");
        switch (shape)
        {
            case "unknown-width": f.Add.NativeArithmeticSize = 0; break;
            case "narrow-width": f.Add.NativeArithmeticSize = 4; break;
            case "interior-offset": f.Add.SetOperand(2, new Immediate(f.Field.Offset + 4)); break;
            case "unknown-offset": f.Add.SetOperand(2, new Immediate(0x100000)); break;
            case "wrong-receiver": f.Receiver.Type = f.Method.AppContext.SystemTypes.SystemObjectType; break;
            case "non-dominating": f.Steps.Remove(f.Add); f.Steps.Add(f.Add); break;
            case "duplicate-definition": f.Steps.Insert(1, new(-1, OpCode.Move, f.Add.Destination!, f.Receiver)); break;
            case "copy-width": f.Copy!.NativeRegisterCopySize = 4; break;
            case "missing-metadata":
                var parent = f.Method.AppContext.SystemTypes.SystemObjectType;
                f.Receiver.Type = new InjectedTypeAnalysisContext(parent.DeclaringAssembly, "Test", "UnknownOwner", parent, TypeAttributes.Public); break;
        }
        f.Method.ControlFlowGraph = new(f.Steps);
        var before = f.Call.Operands.ToArray();
        Assert.That(Arm64AtomicCompareExchangeRecovery.TryRewrite(f.Method, f.Call, true), Is.False, shape);
        Assert.That(f.Call.Operands.ToArray(), Is.EqualTo(before));
    }
}
