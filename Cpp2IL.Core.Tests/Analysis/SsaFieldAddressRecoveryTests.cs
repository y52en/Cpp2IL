using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SsaFieldAddressRecoveryTests
{
    [TestCase("read", true)]
    [TestCase("store", true)]
    [TestCase("addend", true)]
    [TestCase("root-defined", true)]
    [TestCase("narrow-add", false)]
    [TestCase("unknown-add-width", false)]
    [TestCase("unknown-read-width", false)]
    [TestCase("runtime-root", false)]
    [TestCase("unknown-root", false)]
    [TestCase("undefined-root", false)]
    [TestCase("late-root", false)]
    [TestCase("reassigned-root", false)]
    [TestCase("reassigned-pointer", false)]
    [TestCase("negative-offset", false)]
    [TestCase("indexed", false)]
    [TestCase("implicit-root-clobber", false)]
    [TestCase("implicit-pointer-clobber", false)]
    public void OnlyStableKnownObjectAndExactPointerAddAreFolded(string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var holder = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "Holder", t.SystemObjectType, TypeAttributes.Public);
        var root = new LocalVariable("root", new(null, "root"), holder);
        var other = new LocalVariable("other", new(null, "other"), holder);
        var pointer = new LocalVariable("pointer", new(null, "pointer"));
        var value = new LocalVariable("value", new(null, "value"), t.SystemInt32Type);
        var address = new Instruction(1, OpCode.Add, pointer, root, new Immediate(shape == "negative-offset" ? -16 : 16))
            { NativeArithmeticSize = shape == "narrow-add" ? 4 : shape == "unknown-add-width" ? 0 : 8 };
        var memory = new MemoryOperand(pointer, shape == "indexed" ? value : null, shape == "addend" ? 4 : 0, shape == "indexed" ? 4 : 0);
        var access = shape == "store" ? new Instruction(2, OpCode.Move, memory, value) { NativeWriteSize = 4 }
            : new Instruction(2, OpCode.Move, value, memory) { NativeReadSize = shape == "unknown-read-width" ? 0 : 4 };
        var instructions = new List<Instruction> { address, access, new(3, OpCode.Return, value) };
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Caller", t.SystemInt32Type, MethodAttributes.Public | MethodAttributes.Static, [])
            { ParameterLocals = [root, other, value], Locals = [root, other, pointer, value] };
        if (shape == "runtime-root") root.Type = new RuntimeClassTypeAnalysisContext(holder, holder.DeclaringAssembly);
        if (shape == "unknown-root") root.Type = null;
        if (shape == "undefined-root") method.ParameterLocals = [other, value];
        if (shape is "root-defined" or "late-root")
        {
            method.ParameterLocals = [other, value];
            instructions.Insert(shape == "late-root" ? 1 : 0, new(0, OpCode.Move, root, other));
        }
        if (shape == "reassigned-root") instructions.Insert(1, new(4, OpCode.Move, root, other));
        if (shape == "reassigned-pointer") instructions.Insert(1, new(4, OpCode.Move, pointer, new Immediate(0)));
        if (shape is "implicit-root-clobber" or "implicit-pointer-clobber")
            instructions.Insert(1, new Instruction(4, OpCode.CallVoid, new StringLiteral("opaque"))
                { ImplicitDefinition = shape == "implicit-root-clobber" ? root.Register : pointer.Register });
        method.ControlFlowGraph = new(instructions);
        var original = access.Operands[shape == "store" ? 0 : 1];
        Assert.That(SsaFieldAddressRecovery.Run(method), Is.EqualTo(expected ? 1 : 0));
        if (!expected) Assert.That(access.Operands[shape == "store" ? 0 : 1], Is.SameAs(original));
        else
        {
            var recovered = (MemoryOperand)access.Operands[shape == "store" ? 0 : 1];
            Assert.That(recovered.Base, Is.SameAs(root));
            Assert.That(recovered.Addend, Is.EqualTo(shape == "addend" ? 20 : 16));
            Assert.That(method.ControlFlowGraph.Instructions.Contains(address), Is.True);
        }
    }
}
