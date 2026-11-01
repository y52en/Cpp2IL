using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class TrivialConstructorRecoveryTests
{
    [TestCase("late-local")]
    [TestCase("runtime-handle")]
    [TestCase("unknown")]
    [TestCase("already-normalized")]
    public void LateAllocationMetadataIsNormalizedOnceWithoutResettingWidenedResult(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var type=app.SystemTypes.SystemStringType;
        var owner=new InjectedTypeAnalysisContext(type.DeclaringAssembly,"Test","LateAllocation",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var method=owner.InjectMethodContext("Probe",app.SystemTypes.SystemVoidType,MethodAttributes.Public | MethodAttributes.Static);
        var result=new LocalVariable("result",new Register(null,"result"),app.SystemTypes.SystemObjectType);
        var local=new LocalVariable("handle",new Register(null,"handle"));
        var runtime=new RuntimeClassTypeAnalysisContext(type,type.DeclaringAssembly);
        IOperand operand=shape switch { "runtime-handle"=>runtime,"already-normalized"=>type,_=>local };
        var allocation=new Instruction(0,OpCode.Newobj,result,operand);
        method.ControlFlowGraph=new([allocation,new(1,OpCode.Return)]);
        if(shape=="late-local")
        {
            Assert.That(LocalVariables.NormalizePendingAllocations(method),Is.False);
            local.Type=runtime;
        }
        var expected=shape is "late-local" or "runtime-handle";
        Assert.That(LocalVariables.NormalizePendingAllocations(method),Is.EqualTo(expected));
        Assert.That(allocation.Operands[1],expected ? Is.SameAs(type) : Is.SameAs(operand));
        Assert.That(result.Type,expected ? Is.SameAs(type) : Is.SameAs(app.SystemTypes.SystemObjectType));
        result.Type=app.SystemTypes.SystemObjectType;
        Assert.That(LocalVariables.NormalizePendingAllocations(method),Is.False);
        Assert.That(result.Type,Is.SameAs(app.SystemTypes.SystemObjectType));
    }

    [TestCase("direct")]
    [TestCase("class-handle")]
    [TestCase("class-local")]
    [TestCase("unknown-local")]
    [TestCase("integer")]
    public void AllocationTypeComesOnlyFromItsOwnKnownMetadataOperand(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var expected = app.SystemTypes.SystemStringType;
        var runtime = new RuntimeClassTypeAnalysisContext(expected, expected.DeclaringAssembly);
        IOperand operand = shape switch
        {
            "direct" => expected,
            "class-handle" => runtime,
            "class-local" => new LocalVariable("class", new Register(null, "class"), runtime),
            "unknown-local" => new LocalVariable("unknown", new Register(null, "unknown"), app.SystemTypes.SystemObjectType),
            _ => new Immediate(123),
        };
        Assert.That(TrivialConstructorRecovery.AllocationType(operand),
            shape is "unknown-local" or "integer" ? Is.Null : Is.SameAs(expected));
    }

    [Test]
    public void NewobjSeedingPromotesExactClassHandleButLeavesUnknownOperandUnchanged()
    {
        var app = TestGameLoader.LoadSimple2019Game(); var type = app.SystemTypes.SystemStringType;
        var owner = new InjectedTypeAnalysisContext(type.DeclaringAssembly,
            "Test", "AllocationProbe", app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var method = owner.InjectMethodContext("Probe", app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemObjectType);
        var handle = new LocalVariable("handle", new Register(null, "handle"), new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
        var unknown = new LocalVariable("unknown", new Register(null, "unknown"));
        var a = new Instruction(0, OpCode.Newobj, result, handle);
        var b = new Instruction(1, OpCode.Newobj, new LocalVariable("other", new Register(null, "other")), unknown);
        method.ControlFlowGraph = new([a, b, new(2, OpCode.Return)]);
        typeof(LocalVariables).GetMethod("SeedNewobjResults", BindingFlags.NonPublic | BindingFlags.Static)!.Invoke(null, new object[] { method });
        Assert.That(a.Operands[1], Is.SameAs(type));
        Assert.That(result.Type, Is.SameAs(type));
        Assert.That(b.Operands[1], Is.SameAs(unknown));
    }

    [TestCase("valid")]
    [TestCase("wrong-base")]
    [TestCase("virtual")]
    [TestCase("extra-store")]
    [TestCase("different-call")]
    [TestCase("intervening-effect")]
    public void CompleteDirectBaseForwardingPreservesBaseEffectsAndRejectsGuesses(string shape)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var types = app.SystemTypes;
        var parent = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "EffectfulBase", types.SystemObjectType, TypeAttributes.Public);
        var owner = new InjectedTypeAnalysisContext(parent.DeclaringAssembly, "Test", "Forwarder", parent, TypeAttributes.Public);
        var baseCtor = parent.InjectMethodContext(".ctor", types.SystemVoidType, MethodAttributes.Public);
        var other = types.SystemObjectType.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var ctor = owner.InjectMethodContext(".ctor", types.SystemVoidType, MethodAttributes.Public);
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        ctor.ParameterLocals = [self]; ctor.Locals = [self];
        var forwarding = new Instruction(0, OpCode.CallVoid, baseCtor, self) { NativeVirtualDispatch = shape == "virtual" };
        if (shape == "wrong-base") owner.BaseType = types.SystemObjectType;
        ctor.ControlFlowGraph = shape == "extra-store"
            ? new([forwarding, new(1, OpCode.Move, new MemoryOperand(self, addend:16), new Immediate(1)), new(2, OpCode.Return)])
            : new([forwarding, new(2, OpCode.Return)]);
        var template = TrivialConstructorRecovery.Extract(ctor);
        if (shape is "wrong-base" or "virtual" or "extra-store")
        { Assert.That(template, Is.Null); return; }
        Assert.That(template!.ForwardedBase, Is.SameAs(baseCtor));
        owner.PutExtraData(TrivialConstructorRecovery.CacheKey, new[] { template });
        var obj = new LocalVariable("obj", new Register(null, "obj"), owner);
        var allocation = new Instruction(0, OpCode.Newobj, obj, owner);
        var call = new Instruction(2, OpCode.CallVoid, shape == "different-call" ? other : baseCtor, obj);
        var following = new Instruction(3, OpCode.CallVoid, new StringLiteral("following effect"));
        var caller = owner.InjectMethodContext("Caller", types.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
        caller.ControlFlowGraph = shape == "intervening-effect"
            ? new([allocation, new(1, OpCode.CallVoid, new StringLiteral("intervening effect")), call, following, new(4, OpCode.Return)])
            : new([allocation, call, following, new(4, OpCode.Return)]);
        Assert.That(TrivialConstructorRecovery.Run(caller), Is.EqualTo(shape == "valid" ? 1 : 0));
        Assert.That(call.Operands[0], Is.SameAs(shape == "valid" ? ctor : shape == "different-call" ? other : baseCtor));
        Assert.That(following.OpCode, Is.EqualTo(OpCode.CallVoid));
    }

    private static (InjectedTypeAnalysisContext Type, InjectedMethodAnalysisContext Ctor, MethodAnalysisContext Base) Fixture()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var types = app.SystemTypes;
        var parent = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Test", "Parent", types.SystemObjectType, TypeAttributes.Public);
        var type = new InjectedTypeAnalysisContext(parent.DeclaringAssembly, "Test", "Derived", parent, TypeAttributes.Public);
        var ctor = type.InjectMethodContext(".ctor", types.SystemVoidType, MethodAttributes.Public, []);
        var self = new LocalVariable("this", new Register(null, "this"), type) { IsThis = true };
        var baseCtor = types.SystemObjectType.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        baseCtor.PutExtraData(TrivialConstructorRecovery.ObjectProofKey, new TrivialConstructorRecovery.ObjectProof(true));
        ctor.ParameterLocals = [self]; ctor.Locals = [self];
        ctor.ControlFlowGraph = new([new(0, OpCode.CallVoid, baseCtor, self), new(1, OpCode.Return)]);
        return (type, ctor, baseCtor);
    }

    [Test]
    public void CompleteNoOpBodySupportsAnIndirectBaseType()
    {
        var fixture = Fixture();
        Assert.That(TrivialConstructorRecovery.Extract(fixture.Ctor), Is.Not.Null);
        fixture.Base.PutExtraData(TrivialConstructorRecovery.ObjectProofKey, new TrivialConstructorRecovery.ObjectProof(false));
        Assert.That(TrivialConstructorRecovery.Extract(fixture.Ctor), Is.Null);
    }

    [TestCase("callback")]
    [TestCase("store")]
    [TestCase("missing-return")]
    [TestCase("another-object")]
    public void ObservableOrIncompleteConstructorIsRejected(string shape)
    {
        var f = Fixture();
        var cfg = f.Ctor.ControlFlowGraph!;
        var instructions = cfg.Blocks.Single(b => b.Instructions.Any(i => i.OpCode == OpCode.CallVoid)).Instructions;
        if (shape == "missing-return")
        {
            var returned = cfg.Blocks.Single(b => b.Instructions.Any(i => i.OpCode == OpCode.Return)).Instructions;
            returned.RemoveAll(i => i.OpCode == OpCode.Return);
        }
        else if (shape == "another-object") instructions[0].SetOperand(1,
            new LocalVariable("other", new Register(null, "other"), f.Type));
        else instructions.Insert(1, shape == "callback" ? new Instruction(2, OpCode.CallVoid, new StringLiteral("callback"))
            : new Instruction(2, OpCode.Move, new MemoryOperand(f.Ctor.ParameterLocals[0], addend: 16), new Immediate(1)));
        Assert.That(TrivialConstructorRecovery.Extract(f.Ctor), Is.Null);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AllocatedTypeConstructorIsRecoveredWithoutRemovingCallerWrites(bool alias)
    {
        var f = Fixture();
        var template = TrivialConstructorRecovery.Extract(f.Ctor)!;
        f.Type.PutExtraData(TrivialConstructorRecovery.CacheKey, new[] { template });
        var obj = new LocalVariable("obj", new Register(null, "obj"), f.Type);
        var copy = new LocalVariable("copy", new Register(null, "copy"), f.Type);
        var allocation = new Instruction(0, OpCode.Newobj, obj, f.Type);
        var call = new Instruction(2, OpCode.CallVoid, f.Base, alias ? copy : obj);
        var store = new Instruction(3, OpCode.Move, new MemoryOperand(obj, addend: 16), new Immediate(42));
        var caller = f.Type.InjectMethodContext("Caller", f.Ctor.ReturnType, MethodAttributes.Public | MethodAttributes.Static, []);
        caller.ControlFlowGraph = new(alias ? [allocation, new(1, OpCode.Move, copy, obj), call, store, new(4, OpCode.Return)]
            : [allocation, call, store, new(4, OpCode.Return)]);
        Assert.That(TrivialConstructorRecovery.Run(caller), Is.EqualTo(1));
        Assert.That(call.Operands[0], Is.SameAs(f.Ctor));
        Assert.That(store.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((Immediate)store.Operands[1]).Value, Is.EqualTo(42));
    }

    [TestCase("callback")]
    [TestCase("unproven-base")]
    [TestCase("ambiguous")]
    public void UnsafeCallsiteRemainsUnchanged(string shape)
    {
        var f = Fixture(); var template = TrivialConstructorRecovery.Extract(f.Ctor)!;
        f.Type.PutExtraData(TrivialConstructorRecovery.CacheKey,
            shape == "ambiguous" ? new[] { template, template } : new[] { template });
        if (shape == "unproven-base") f.Base.PutExtraData(TrivialConstructorRecovery.ObjectProofKey,
            new TrivialConstructorRecovery.ObjectProof(false));
        var obj = new LocalVariable("obj", new Register(null, "obj"), f.Type);
        var allocation = new Instruction(0, OpCode.Newobj, obj, f.Type);
        var call = new Instruction(2, OpCode.CallVoid, f.Base, obj);
        var caller = f.Type.InjectMethodContext("Caller", f.Ctor.ReturnType, MethodAttributes.Public | MethodAttributes.Static, []);
        caller.ControlFlowGraph = new(shape == "callback" ? [allocation, new(1, OpCode.CallVoid, new StringLiteral("callback")), call, new(3, OpCode.Return)]
            : [allocation, call, new(3, OpCode.Return)]);
        Assert.That(TrivialConstructorRecovery.Run(caller), Is.Zero);
        Assert.That(call.Operands[0], Is.SameAs(f.Base));
    }

    [Test]
    public void SameNameDoesNotProveConstructorOwnerIdentity()
    {
        var f = Fixture();
        var impostor = new InjectedTypeAnalysisContext(f.Type.DeclaringAssembly, "Test", "Derived", f.Type.BaseType!, TypeAttributes.Public);
        Assert.That(impostor.FullName, Is.EqualTo(f.Type.FullName));
        Assert.That(TrivialConstructorRecovery.SameType(impostor, f.Type), Is.False);
    }

    [Test]
    public void GenericConstructorBindsOnlyTheExactDefinitionToKnownAllocationArguments()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Collections.Generic.List`1");
        var constructor = definition.Methods.Single(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var allocation = definition.MakeGenericInstanceType([app.SystemTypes.SystemInt32Type]);
        var bound = TrivialConstructorRecovery.BindConstructorOwner(constructor, allocation);
        Assert.That(bound, Is.Not.Null);
        Assert.That(TrivialConstructorRecovery.SameType(bound!.DeclaringType, allocation), Is.True);
        var wrong = app.SystemTypes.SystemObjectType.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        Assert.That(TrivialConstructorRecovery.BindConstructorOwner(wrong, allocation), Is.Null);
    }
}
