using System;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// isinst + the inspected native cast-message/exception transport. Unlike a
// general isinst, this check throws on failure. Preserve the preceding null
// guard: castclass alone does NOT throw for null.
public static class RuntimeCheckedCastRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.ControlFlowGraph is not { } cfg) return 0;
        var count = 0;
        foreach (var block in cfg.Blocks.ToArray())
            if (cfg.Blocks.Contains(block) && TryRecover(method, block, a => InlineClassCastRecovery.IsMessageBuilder(method, a))) count++;
        if (count > 0) { cfg.RemoveUnreachableBlocks(); DeadCodeEliminator.Run(method); }
        return count;
    }

    internal static bool TryRecover(MethodAnalysisContext method, Block guard, Func<ulong, bool> helper)
    {
        var cfg = method.ControlFlowGraph!;
        // Deliberately accept only this complete, side-effect-free guard.
        var check = guard.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (check is not [Instruction { OpCode: OpCode.IsInst, Operands: [LocalVariable result, TypeAnalysisContext target, LocalVariable source] } cast,
            Instruction { OpCode: OpCode.CheckEqual, Operands: [LocalVariable flag, var tested, Immediate { Value: 0 }] },
            Instruction { OpCode: OpCode.ConditionalJump, Operands: [Block failure, var condition] }]
            || !ReferenceEquals(tested, result) || !ReferenceEquals(condition, flag)
            || source.Type is not { IsValueType: false } || target.IsValueType
            || source.Type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
            || target is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
            || guard.Successors.Count != 2 || guard.Successors.Distinct().Count() != 2
            || !guard.Successors.Contains(failure) || failure.Predecessors.Count != 1
            || !ReferenceEquals(failure.Predecessors[0], guard) || guard.Predecessors.Count != 1) return false;
        var success = guard.Successors.Single(b => !ReferenceEquals(b, failure));
        if (success.Predecessors.Count != 1 || !ReferenceEquals(success.Predecessors[0], guard)
            || cfg.Instructions.Count(i => ReferenceEquals(i.Destination, result)) != 1
            || cfg.Instructions.Count(i => ReferenceEquals(i.Destination, flag)) != 1) return false;
        var before = guard.Predecessors[0];
        // Exact non-null predecessor; no guessed dominance from register names.
        if (before.Successors.Count != 2 || !before.Successors.Contains(guard)
            || before.Instructions.TakeLast(2).ToArray() is not
            [Instruction { OpCode: OpCode.CheckEqual, Operands: [LocalVariable nullFlag, var nullObject, Immediate { Value: 0 }] },
             Instruction { OpCode: OpCode.ConditionalJump, Operands: [Block nullExit, var nullCondition] }]
            || !ReferenceEquals(nullObject, source) || !ReferenceEquals(nullCondition, nullFlag)
            || ReferenceEquals(nullExit, guard) || !before.Successors.Contains(nullExit)
            || cfg.Instructions.Count(i => ReferenceEquals(i.Destination, nullFlag)) != 1) return false;
        var nullBody = nullExit.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        // The inspected IntrospectionExtensions.GetTypeInfo also uses this
        // exact non-null cast guard, but returns null on the preceding null
        // edge. Keep that edge and its return intact. It is not a merge into
        // success, an arbitrary return value, or a nullable value-type result.
        var nullThrows = nullBody is [Instruction { OpCode: OpCode.Throw,
            Operands: [TypeAnalysisContext { FullName: "System.NullReferenceException" }] }];
        var nullReturns = nullBody is [Instruction { OpCode: OpCode.Return,
            Operands: [Immediate { Value: 0 }] }]
            && NullBypassRuntimeCastRecovery.ReferenceType(method.ReturnType);
        if ((!nullThrows && !nullReturns) || nullExit.Successors.Count != 1
            || !ReferenceEquals(nullExit.Successors[0], cfg.ExitBlock)) return false;
        if (!InlineClassTestRecovery.StableSource(method, source, guard)) return false;

        var body = failure.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (body is not
            [Instruction { OpCode: OpCode.Move, NativeReadSize: 8, Operands: [LocalVariable klass, MemoryOperand { Base: var obj, Addend: 0, Index: null, Scale: 0 }] },
             Instruction { OpCode: OpCode.Move, NativeReadSize: 8, Operands: [LocalVariable name, MemoryOperand { Base: var classBase, Addend: 0x40, Index: null, Scale: 0 }] },
             Instruction { OpCode: OpCode.Call, Operands: [Immediate { Value: >= 0 } address, LocalVariable builderResult, var fromClass, var toClass, ..] },
             Instruction { OpCode: OpCode.Newobj, Operands: [LocalVariable exception, TypeAnalysisContext { FullName: "System.InvalidCastException" }] }]
            || !ReferenceEquals(obj, source) || !ReferenceEquals(classBase, klass)
            || !ReferenceEquals(fromClass, name) || !ReferenceEquals(toClass, target)
            || !helper((ulong)address.Value) || failure.Successors.Count != 1) return false;
        var transport = failure.Successors[0];
        if (transport.Predecessors.Count != 1 || !ReferenceEquals(transport.Predecessors[0], failure)
            || transport.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray() is not
                [Instruction { OpCode: OpCode.Throw, Operands: [var thrown] }]
            || !ReferenceEquals(thrown, exception) || transport.Successors.Count != 1
            || !ReferenceEquals(transport.Successors[0], cfg.ExitBlock)) return false;
        var removed = new[] { klass, name, builderResult, exception, flag };
        // No deleted metadata/result/predicate may escape, including nested bases.
        if (cfg.Blocks.Where(b => !ReferenceEquals(b, guard) && !ReferenceEquals(b, failure) && !ReferenceEquals(b, transport))
            .SelectMany(b => b.Instructions).SelectMany(i => i.Operands)
            .Any(o => removed.Any(v => Contains(o, v)))) return false;
        cast.OpCode = OpCode.CastClass;
        guard.Instructions = [cast, new(check[^1].Index, OpCode.Jump, success)];
        cfg.RemoveEdge(guard, failure);
        guard.CalculateBlockType();
        return true;
    }

    internal static bool Contains(IOperand operand, LocalVariable value) => operand switch
    {
        LocalVariable local => ReferenceEquals(local, value),
        MemoryOperand memory => memory.Base != null && Contains(memory.Base, value)
            || memory.Index != null && Contains(memory.Index, value),
        FieldReference field => ReferenceEquals(field.Local, value) || field.Parent != null && Contains(field.Parent, value),
        ArrayAccess array => ReferenceEquals(array.Array, value) || Contains(array.Index, value),
        ArrayLength array => ReferenceEquals(array.Array, value),
        AddressOf address => Contains(address.Target, value),
        _ => false
    };
}
