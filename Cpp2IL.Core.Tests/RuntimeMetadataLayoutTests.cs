using System.Collections.Generic;
using System.Linq;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class RuntimeMetadataLayoutTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static RuntimeMetadataLayout Legacy => RuntimeMetadataLayout.For(new UnityVersion(2018, 4, 28, UnityVersionType.Final, 1), 8);

    [Test]
    public void Unity2018Arm64_UsesMatchingHeaderOffsets()
    {
        Assert.That(Legacy, Is.EqualTo(new RuntimeMetadataLayout(0x126, 0x128, 0x18, 0x30, 0xC0, 0xB8)));
    }

    [TestCase(2018, 4, 4)]
    [TestCase(2018, 3, 8)]
    [TestCase(2019, 4, 8)]
    [TestCase(2022, 3, 8)]
    public void OtherProfiles_PreserveUpstreamAssumptions(int major, int minor, int pointerSize)
    {
        var layout = RuntimeMetadataLayout.For(new UnityVersion((ushort)major, (ushort)minor, 1, UnityVersionType.Final, 1), pointerSize);
        Assert.That(layout.VTable, Is.EqualTo(pointerSize == 4 ? 0xC0 : 0x138));
        Assert.That(layout.MethodClass, Is.EqualTo(pointerSize == 4 ? 0x10 : 0x20));
    }

    private static InjectedMethodAnalysisContext Context(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var context = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        context.Locals = locals.ToList();
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        return context;
    }

    [TestCase(0x18, true)]
    [TestCase(0x20, false)]
    [TestCase(0x30, false)]
    public void LegacyMethodInfo_ResolvesOnlyItsActualClassField(int offset, bool resolves)
    {
        var method = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType.Methods.First();
        var handle = new RuntimeMethodInfoAnalysisContext(method, method.DeclaringType!.DeclaringAssembly);
        var source = new LocalVariable("methodInfo", new Register(null, "source"), handle);
        var result = new LocalVariable("klass", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result, new MemoryOperand(source, addend: offset));
        var changed = RgctxResolver.Run(Context([load, new(1, OpCode.Return)], source, result), Legacy);
        Assert.That(changed, Is.EqualTo(resolves));
        if (resolves)
            Assert.That(((RuntimeClassTypeAnalysisContext)load.Operands[1]).RepresentedType, Is.SameAs(method.DeclaringType));
        else
            Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [TestCase(0)]
    [TestCase(1)]
    public void LegacyVirtualDispatch_UsesCorrectSlotAndMethodInfo(int delta)
    {
        var owner = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType;
        var target = owner.Methods.First(m => m.Definition is { slot: < ushort.MaxValue } && !m.IsVoid);
        var klass = new LocalVariable("klass", new Register(null, "klass"), new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var receiver = new LocalVariable("this", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"));
        var offset = Legacy.VTable + target.Definition!.slot * 16 + delta;
        var call = new Instruction(0, OpCode.IndirectCall, new MemoryOperand(klass, addend: offset), result,
            receiver, new MemoryOperand(klass, addend: offset + 8));
        var changed = MetadataResolver.ResolveVirtualCalls(Context([call, new(1, OpCode.Return)], klass, receiver, result), Legacy);
        Assert.That(changed, Is.EqualTo(delta == 0));
        if (delta == 0)
        {
            Assert.That(call.Operands[0], Is.SameAs(target));
            Assert.That(call.Operands.Any(o => o is RuntimeMethodInfoAnalysisContext info && ReferenceEquals(info.RepresentedMethod, target)), Is.True);
        }
        else
            Assert.That(call.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [TestCase(true, 0x126, 1, true)]
    [TestCase(false, 0x126, 1, false)]
    [TestCase(true, 0x127, 2, false)]
    [TestCase(true, 0x135, 1, false)]
    public void LegacyInitGuard_RequiresRuntimeClassAndActualNoErrorBit(bool runtimeClass, int offset, int mask, bool removed)
    {
        var owner = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType;
        var klass = new LocalVariable("klass", new Register(null, "klass"),
            runtimeClass ? new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly) : owner);
        var flag = new LocalVariable("flag", new Register(null, "flag"));
        var merge = new Instruction(4, OpCode.CallVoid, new StringLiteral("managed-effect"));
        var init = new Instruction(2, OpCode.CallVoid, new Immediate(0x100), klass);
        var context = Context([
            new(0, OpCode.And, flag, new MemoryOperand(klass, addend: offset), new Immediate(mask)),
            new(1, OpCode.ConditionalJump, merge, flag), init,
            new(3, OpCode.Jump, merge), merge, new(5, OpCode.Return)
        ], klass, flag);
        MetadataInitGuardRemover.Run(context.ControlFlowGraph!, Legacy.InitializedFlag);
        Assert.That(context.ControlFlowGraph!.Instructions.Contains(init), Is.EqualTo(!removed));
        Assert.That(context.ControlFlowGraph.Instructions.Contains(merge), Is.True, "application effects must remain");
    }
}
