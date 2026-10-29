using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class VirtualTailArrayIdentityTests
{
    [TestCase("same-vector", true)]
    [TestCase("different-element", false)]
    [TestCase("same-name-impostor", false)]
    [TestCase("rank-one-array", false)]
    [TestCase("pointer", false)]
    public void EncodingTailRequiresExactElementMetadataAndArrayShape(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        app.InstructionSet = new NewArmV8InstructionSet();
        var owner = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Text.Encoding");
        var target = owner.Methods.Single(m => m.Name == "GetBytes" && m.Parameters.Count == 1
            && m.Parameters[0].ParameterType == app.SystemTypes.SystemStringType
            && m.ReturnType is SzArrayTypeAnalysisContext && m.Definition is {slot: < ushort.MaxValue});
        var element = ((SzArrayTypeAnalysisContext)target.ReturnType).ElementType;
        TypeAnalysisContext callerReturn = shape switch {
            "different-element" => new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType),
            "same-name-impostor" => new SzArrayTypeAnalysisContext(new InjectedTypeAnalysisContext(
                element.DeclaringAssembly, element.Namespace, element.Name, app.SystemTypes.SystemObjectType, TypeAttributes.Public)),
            "rank-one-array" => new ArrayTypeAnalysisContext(element, 1),
            "pointer" => new PointerTypeAnalysisContext(element),
            _ => new SzArrayTypeAnalysisContext(element)
        };
        Assert.That(callerReturn, Is.Not.SameAs(target.ReturnType));
        var method = new InjectedMethodAnalysisContext(owner, "ArrayTail", callerReturn,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var klass = new LocalVariable("klass", new Register(null, "X8"),
            new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var receiver = new LocalVariable("receiver", new Register(null, "X0"), owner);
        var argument = new LocalVariable("text", new Register(null, "X1"), app.SystemTypes.SystemStringType);
        var info = new LocalVariable("info", new Register(null, "X2"));
        var pointer = new LocalVariable("pointer", new Register(null, "X3"));
        var layout = RuntimeMetadataLayout.For(new UnityVersion(2018, 4, 28, UnityVersionType.Final, 1), 8);
        var offset = layout.VTable + target.Definition!.slot * 16;
        var jump = new Instruction(2, OpCode.IndirectJump, pointer, receiver);
        var raw = new List<IOperand> { receiver, argument, info, pointer };
        raw.AddRange(Enumerable.Range(4, 4).Select(i => (IOperand)new LocalVariable("arg" + i, new Register(null, "X" + i))));
        raw.AddRange(Enumerable.Range(0, 8).Select(i => (IOperand)new LocalVariable("float" + i, new Register(null, "V" + i))));
        jump.AddOperands(raw);
        method.ControlFlowGraph = new([
            new(0, OpCode.Move, pointer, new MemoryOperand(klass, addend: offset)),
            new(1, OpCode.Move, info, new MemoryOperand(klass, addend: offset + 8)), jump]);
        method.Locals = [klass, receiver, argument, info, pointer];
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];
        Assert.That(MetadataResolver.ResolveVirtualCalls(method, layout), Is.EqualTo(expected));
        if (!expected) {
            Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
            Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Return), Is.False);
            return;
        }
        Assert.That(jump.NativeVirtualDispatch, Is.True);
        Assert.That(jump.Operands[0], Is.SameAs(target));
        Assert.That(jump.Operands[2], Is.SameAs(receiver));
        Assert.That(jump.Operands[3], Is.SameAs(argument));
        Assert.That(jump.Operands.Count, Is.EqualTo(5));
        Assert.That(method.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.Return).Operands.Single(),
            Is.SameAs(jump.Destination));
        Assert.That(MetadataResolver.ResolveVirtualCalls(method, layout), Is.False);
    }
}
