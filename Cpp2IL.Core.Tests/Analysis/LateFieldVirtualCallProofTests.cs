using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateFieldVirtualCallProofTests
{
    [TestCase("valid", true)]
    [TestCase("already-typed", true)]
    [TestCase("wrong-receiver", false)]
    [TestCase("duplicate-receiver", false)]
    [TestCase("duplicate-class", false)]
    [TestCase("duplicate-pointer", false)]
    [TestCase("narrow-receiver", false)]
    [TestCase("narrow-class", false)]
    [TestCase("narrow-pointer", false)]
    [TestCase("class-offset", false)]
    [TestCase("slot-alignment", false)]
    [TestCase("unknown-slot", false)]
    [TestCase("wrong-layout", false)]
    [TestCase("wrong-field-offset", false)]
    [TestCase("wrong-field-owner", false)]
    [TestCase("conflicting-receiver-type", false)]
    [TestCase("conflicting-class-type", false)]
    [TestCase("conflicting-result-type", false)]
    [TestCase("implicit-clobber", false)]
    [TestCase("address-escape", false)]
    [TestCase("not-dominating", false)]
    [TestCase("root-reassigned", false)]
    [TestCase("indexed-pointer", false)]
    [TestCase("nested-field", false)]
    [TestCase("tail-call", false)]
    [TestCase("root-address-escape", false)]
    public void LateDispatchRequiresUniqueDominatingOriginalMetadataLoads(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); app.InstructionSet = new NewArmV8InstructionSet();
        var objectType = app.SystemTypes.SystemObjectType;
        var field = app.Assemblies.SelectMany(a => a.Types).Where(t => !t.IsValueType)
            .SelectMany(t => t.Fields).First(f => !f.IsStatic && f.Offset >= 16
                && f.FieldType.FullName == "System.String" && f.BackingData != null);
        var receiverType = field.FieldType;
        LocalVariable Local(string n, TypeAnalysisContext? type = null) => new(n, new(null, n), type);
        var root = Local("owner", field.DeclaringType);
        var receiver = Local("receiver"); var klass = Local("klass"); var pointer = Local("pointer");
        var result = Local("result"); var other = Local("other", objectType);
        var target = objectType.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0);
        var layout = RuntimeMetadataLayout.For(new UnityVersion(2018, 4, 28, UnityVersionType.Final, 1), 8);
        var offset = layout.VTable + target.Definition!.slot * 16;
        var fieldReference = new FieldReference(field, root, field.Offset);
        var receiverLoad = new Instruction(1, OpCode.Move, receiver, fieldReference) { NativeReadSize = 8 };
        var classLoad = new Instruction(2, OpCode.Move, klass, new MemoryOperand(receiver)) { NativeReadSize = 8 };
        var pointerLoad = new Instruction(3, OpCode.Move, pointer, new MemoryOperand(klass, addend: offset)) { NativeReadSize = 8 };
        var call = new Instruction(4, OpCode.IndirectCall, pointer, result, receiver,
            new MemoryOperand(klass, addend: offset + 8));
        var cfg = new ISILControlFlowGraph([receiverLoad, classLoad, pointerLoad, call, new(5, OpCode.Return, result)]);
        var body = cfg.Blocks.Single(b => b.Instructions.Contains(call));
        var method = new InjectedMethodAnalysisContext(field.DeclaringType, "Caller", app.SystemTypes.SystemStringType,
            MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = cfg, ParameterLocals = [root, other], Locals = [root, receiver, klass, pointer, result, other] };
        if (shape == "already-typed")
        { receiver.Type = receiverType; klass.Type = new RuntimeClassTypeAnalysisContext(receiverType, receiverType.DeclaringAssembly); }
        if (shape == "wrong-receiver") call.SetOperand(2, other);
        if (shape == "duplicate-receiver") body.Instructions.Insert(0, new(0, OpCode.Move, receiver, other));
        if (shape == "duplicate-class") body.Instructions.Insert(0, new(0, OpCode.Move, klass, other));
        if (shape == "duplicate-pointer") body.Instructions.Insert(0, new(0, OpCode.Move, pointer, other));
        if (shape == "narrow-receiver") receiverLoad.NativeReadSize = 4;
        if (shape == "narrow-class") classLoad.NativeReadSize = 4;
        if (shape == "narrow-pointer") pointerLoad.NativeReadSize = 4;
        if (shape == "class-offset") classLoad.SetOperand(1, new MemoryOperand(receiver, addend: 8));
        if (shape == "slot-alignment") pointerLoad.SetOperand(1, new MemoryOperand(klass, addend: offset + 1));
        if (shape == "unknown-slot") pointerLoad.SetOperand(1, new MemoryOperand(klass, addend: 0x100000));
        if (shape == "wrong-layout") layout = layout with { VTable = 0x138 };
        if (shape == "wrong-field-offset") fieldReference.Offset++;
        if (shape == "wrong-field-owner") root.Type = objectType;
        if (shape == "conflicting-receiver-type") receiver.Type = objectType;
        if (shape == "conflicting-class-type") klass.Type = objectType;
        if (shape == "conflicting-result-type") result.Type = objectType;
        if (shape == "implicit-clobber") body.Instructions.Insert(3, new(0, OpCode.Nop) { ImplicitDefinition = receiver.Register });
        if (shape == "address-escape") body.Instructions.Insert(3, new(0, OpCode.CallVoid, new Immediate(1234), new AddressOf(klass)));
        if (shape == "not-dominating") { body.Instructions.Remove(pointerLoad); body.Instructions.Add(pointerLoad); }
        if (shape == "root-reassigned") body.Instructions.Insert(0, new(0, OpCode.Move, root, other));
        if (shape == "indexed-pointer") pointerLoad.SetOperand(1, new MemoryOperand(klass, other, offset, 8));
        if (shape == "nested-field") fieldReference.Parent = new FieldReference(field, root, field.Offset);
        if (shape == "tail-call") call.OpCode = OpCode.IndirectJump;
        if (shape == "root-address-escape") body.Instructions.Insert(3, new(0, OpCode.CallVoid, new Immediate(1234), new AddressOf(new MemoryOperand(root))));
        var before = cfg.Instructions.Select(i => i.ToString()).ToArray();
        var proof = MetadataResolver.ProveLateFieldVirtualCall(method, call, layout);
        Assert.That(proof != null, Is.EqualTo(expected));
        Assert.That(cfg.Instructions.Select(i => i.ToString()), Is.EqualTo(before));
        if (proof != null)
        {
            Assert.That(proof.Target.Name, Is.EqualTo("ToString"));
            receiver.Type ??= proof.ReceiverType;
            klass.Type ??= new RuntimeClassTypeAnalysisContext(proof.ReceiverType, proof.ReceiverType.DeclaringAssembly);
            Assert.That(MetadataResolver.ResolveVirtualCalls(method, layout, new System.Collections.Generic.HashSet<Instruction> { call }), Is.True);
            Assert.That(call.Operands[0], Is.SameAs(proof.Target));
            Assert.That(call.NativeVirtualDispatch, Is.True);
            var unrelated = new Instruction(6, OpCode.IndirectCall, new MemoryOperand(klass, addend: offset), result, receiver);
            body.Instructions.Add(unrelated);
            Assert.That(MetadataResolver.ResolveVirtualCalls(method, layout, new System.Collections.Generic.HashSet<Instruction>()), Is.False);
            Assert.That(unrelated.OpCode, Is.EqualTo(OpCode.IndirectCall), "late allowlist never licenses unrelated dispatches");
        }
    }
}
