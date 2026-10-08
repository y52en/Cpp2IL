using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClassInitRetryTests
{
    [TestCase("il2cpp_runtime_class_init_actual", true)]
    [TestCase("il2cpp_runtime_class_init_export", true)]
    [TestCase("il2cpp_codegen_runtime_class_init", true)]
    [TestCase("application-callback", false)]
    [TestCase("", false)]
    public void DeadInitArgumentPhi_RetriesOnlyPositivelyKnownCalls(string helper, bool excised)
    {
        var (cfg, branch, init, effect, _) = Graph(helper);
        MetadataInitGuardRemover.Run(cfg, 0x126);
        Assert.That(branch.OpCode, Is.EqualTo(excised ? OpCode.Jump : OpCode.ConditionalJump));
        Assert.That(cfg.Instructions.Contains(init), Is.EqualTo(!excised));
        Assert.That(cfg.Instructions.Contains(effect), Is.True);
        MetadataInitGuardRemover.Run(cfg, 0x126);
        Assert.That(branch.OpCode, Is.EqualTo(excised ? OpCode.Jump : OpCode.ConditionalJump), "repeat is stable");
    }

    [TestCase("callback")]
    [TestCase("store")]
    [TestCase("return")]
    [TestCase("address")]
    [TestCase("memory")]
    [TestCase("indirect")]
    public void Retry_DoesNotEraseEffectsOrEscapingValues(string use)
    {
        var (cfg, branch, init, effect, computed) = Graph("il2cpp_runtime_class_init_actual");
        var initBlock = cfg.Blocks.Find(b => b.Instructions.Contains(init))!;
        if (use == "callback")
            initBlock.Instructions.Insert(initBlock.Instructions.Count - 1, new(20, OpCode.CallVoid, new StringLiteral("application-callback")));
        else if (use == "store")
            initBlock.Instructions.Insert(initBlock.Instructions.Count - 1, new(20, OpCode.Move, new MemoryOperand(addend: 0x1000), new Immediate(1)));
        else
        {
            initBlock.Instructions.Insert(initBlock.Instructions.Count - 1, new(20, OpCode.Move, computed, new Immediate(123)));
            effect.SetOperands(new StringLiteral("application-effect"), use switch
            {
                "address" => new AddressOf(computed),
                "memory" => new MemoryOperand(computed),
                _ => computed
            });
            if (use == "return")
            {
                effect.OpCode = OpCode.Return;
                effect.SetOperands(computed);
            }
            if (use == "indirect")
            {
                effect.OpCode = OpCode.IndirectJump;
                effect.SetOperands(computed);
            }
        }
        MetadataInitGuardRemover.Run(cfg, 0x126);
        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(cfg.Instructions.Contains(init), Is.True);
        Assert.That(init.OpCode, Is.EqualTo(OpCode.Nop), "known runtime call alone is removed");
        Assert.That(cfg.Instructions.Contains(effect), Is.True);
    }

    private static (ISILControlFlowGraph Cfg, Instruction Branch, Instruction Init, Instruction Effect, LocalVariable Computed) Graph(string helper)
    {
        var flag = new LocalVariable("flag", new Register(null, "flag"));
        var argument = new LocalVariable("argument", new Register(null, "arg"));
        var computed = new LocalVariable("computed", new Register(null, "computed"));
        var effect = new Instruction(6, OpCode.CallVoid, new StringLiteral("application-effect"));
        var init = string.IsNullOrEmpty(helper) ? new Instruction(4, OpCode.Nop)
            : new Instruction(4, OpCode.CallVoid, new StringLiteral(helper), argument);
        var branch = new Instruction(1, OpCode.ConditionalJump, effect, flag);
        var cfg = new ISILControlFlowGraph(new List<Instruction>
        {
            new(0, OpCode.CheckEqual, flag, new MemoryOperand(addend: 0x2000), new Immediate(0)),
            branch, new(2, OpCode.Phi, argument, new Immediate(11)),
            new(3, OpCode.Nop), init, new(5, OpCode.Jump, effect), effect, new(7, OpCode.Return)
        });
        return (cfg, branch, init, effect, computed);
    }
}
