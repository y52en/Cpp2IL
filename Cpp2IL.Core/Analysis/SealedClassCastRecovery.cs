using System;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A sealed class has no possible derived instance. Its exact native klass
// comparison, null bypass and proven InvalidCast transport implement castclass.
// Never generalize this to an unsealed class, interface, array or value type.
public static class SealedClassCastRecovery
{
    // A closed metadata-backed generic sealed class is just as exact a native
    // class identity as a non-generic sealed class. Open/partial/malformed
    // instantiations are not proof, even when their definition is sealed.
    private static bool ClosedTarget(TypeAnalysisContext target)
    {
        if (target is not GenericInstanceTypeAnalysisContext generic)
            return target.GenericParameters.Count == 0 && !target.IsGenericInstance;
        return generic.GenericType.Definition != null && !generic.GenericType.IsGenericInstance
            && generic.GenericArguments.Count > 0
            && generic.GenericArguments.Count == generic.GenericType.GenericParameters.Count
            && !generic.HasAnyGenericParameters()
            && generic.GenericArguments.All(a => a is not PointerTypeAnalysisContext
                and not ByRefTypeAnalysisContext and not RuntimeClassTypeAnalysisContext
                and not RuntimeMethodInfoAnalysisContext and not RuntimeFieldInfoAnalysisContext);
    }
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.ControlFlowGraph is not { } cfg) return 0;
        var count = 0;
        foreach (var guard in cfg.Blocks.ToArray())
            if (cfg.Blocks.Contains(guard) && Recover(method, guard,
                address => InlineClassCastRecovery.IsMessageBuilder(method, address))) count++;
        return count;
    }

    internal static bool Recover(MethodAnalysisContext method, Block guard, Func<ulong, bool> helper)
    {
        var cfg = method.ControlFlowGraph!;
        var check = guard.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (check.Length < 3 || check[0] is not { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [LocalVariable klass, MemoryOperand { Base: LocalVariable source, Addend: 0, Index: null, Scale: 0 }] }
            || check[1] is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                Operands: [LocalVariable flag, var testedClass, TypeAnalysisContext target] } compare
            || !ReferenceEquals(testedClass, klass) || !target.IsSealed || target.IsValueType || target.IsInterface
            || target is SzArrayTypeAnalysisContext or PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
            || !ClosedTarget(target)
            || source.Type is not { IsValueType: false }
            || source.Type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
            || check[^1] is not { OpCode: OpCode.ConditionalJump, Operands: [Block branch, var condition] }
            || !ReferenceEquals(condition, flag) || guard.Successors.Count != 2
            || guard.Successors.Distinct().Count() != 2 || !guard.Successors.Contains(branch)
            || guard.Predecessors.Count != 1) return false;
        var success = compare.OpCode == OpCode.CheckEqual ? branch : guard.Successors.Single(b => !ReferenceEquals(b, branch));
        var failure = guard.Successors.Single(b => !ReferenceEquals(b, success));
        bool Copy(Instruction i) => i is { OpCode: OpCode.Move,
            Operands: [LocalVariable { Type.IsValueType: false }, var operand] } && ReferenceEquals(operand, source);
        if (check.Skip(2).SkipLast(1).Any(i => !Copy(i))) return false;
        var before = guard.Predecessors[0];
        var prefix = before.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (before.Successors.Count != 2 || before.Successors.Distinct().Count() != 2 || !before.Successors.Contains(guard)
            || prefix.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block nullBranch, var nullCondition] }
            || !before.Successors.Contains(nullBranch)) return false;
        // A cast preserves null. The null bypass need not be the non-null
        // success: native callers may skip a subsequent member access on null.
        // Keep the entire bypass and its effects; insert castclass immediately
        // before the original null test, after its preceding effects.
        var nullBypass = before.Successors.Single(b => !ReferenceEquals(b, guard));
        var nullChecks = prefix.Where(i => i is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
            Operands: [_, var value, Immediate { Value: 0 }] } && ReferenceEquals(value, source)).ToArray();
        if (nullChecks is not [Instruction nullCheck] || nullCheck.Operands[0] is not LocalVariable nullFlag
            || !ReferenceEquals(nullCondition, nullFlag)
            || (nullCheck.OpCode == OpCode.CheckEqual ? !ReferenceEquals(nullBranch, nullBypass) : !ReferenceEquals(nullBranch, guard))) return false;
        var nullIndex = Array.IndexOf(prefix, nullCheck);
        if (prefix.Skip(nullIndex + 1).SkipLast(1).Any(i => !Copy(i))
            || !InlineClassTestRecovery.StableSource(method, source, guard)
            || new[] { klass, flag, nullFlag }.Any(local => cfg.Instructions.Count(i => ReferenceEquals(i.Destination, local)) != 1)
            || failure.Predecessors.Count != 1 || !ReferenceEquals(failure.Predecessors[0], guard)) return false;
        var body = failure.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (body is not [Instruction { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [LocalVariable name, MemoryOperand { Base: var classBase, Addend: 0x40, Index: null, Scale: 0 }] },
            Instruction { OpCode: OpCode.Call, Operands: [Immediate { Value: >= 0 } address, LocalVariable message, var from, var to, ..] },
            Instruction { OpCode: OpCode.Newobj, Operands: [LocalVariable exception, TypeAnalysisContext { FullName: "System.InvalidCastException" }] }]
            || !ReferenceEquals(classBase, klass) || !ReferenceEquals(from, name) || !ReferenceEquals(to, target)
            || !helper((ulong)address.Value) || failure.Successors.Count != 1) return false;
        var transport = failure.Successors[0];
        if (transport.Predecessors.Count != 1 || !ReferenceEquals(transport.Predecessors[0], failure)
            || transport.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray() is not
                [Instruction { OpCode: OpCode.Throw, Operands: [var thrown] }]
            || !ReferenceEquals(thrown, exception) || transport.Successors.Count != 1
            || !ReferenceEquals(transport.Successors[0], cfg.ExitBlock)) return false;
        var removed = new[] { klass, flag, name, message, exception };
        if (cfg.Blocks.Where(b => !ReferenceEquals(b, guard) && !ReferenceEquals(b, failure) && !ReferenceEquals(b, transport))
            .SelectMany(b => b.Instructions).SelectMany(i => i.Operands)
            .Any(o => removed.Any(local => ForwardNullCheckRecovery.Uses(o, local)))) return false;
        var dominance = new DominatorInfo(cfg);
        // The cast must execute only where this original check executes. A
        // shared success reached without the null predecessor is left alone.
        if (!dominance.Dominates(before, success)) return false;
        var result = new LocalVariable("sealed_cast_" + guard.ID, new(null, "sealed_cast_" + guard.ID), target);
        method.Locals.Add(result);
        var insert = before.Instructions.IndexOf(nullCheck);
        before.Instructions.Insert(insert, new(nullCheck.Index, OpCode.CastClass, result, target, source));
        foreach (var block in cfg.Blocks.Where(b => ReferenceEquals(b, before) || dominance.Dominates(before, b)))
        {
            if (ReferenceEquals(block, failure) || ReferenceEquals(block, transport)) continue;
            var start = ReferenceEquals(block, before) ? insert + 1 : 0;
            foreach (var instruction in block.Instructions.Skip(start))
                for (var i = 0; i < instruction.Operands.Count; i++)
                    if (!ReferenceEquals(instruction.Operands[i], instruction.Destination))
                        instruction.SetOperand(i, InlineClassCastRecovery.Replace(instruction.Operands[i], source, result));
        }
        guard.Instructions = check.Skip(2).SkipLast(1).Append(new(check[^1].Index, OpCode.Jump, success)).ToList();
        cfg.RemoveEdge(guard, failure);
        guard.CalculateBlockType();
        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(method);
        return true;
    }
}
