using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete ShouldRetry @EB4C0C, matching Unity2018 ARM64: two hierarchy tests
// share cached/reloaded class/depth locals after SSA destruction. Resolve EVERY
// incoming definition. Never forward a metadata snapshot through a call/store.
// Keep the depth block's instructions and BOTH application outcomes. Only the
// proven effect-free ancestor kernel is unlinked; escaping copies need an
// identical assignment already executed in the surviving depth block.
public static class SharedClassTestRecovery
{
    public static int Run(MethodAnalysisContext method)
        => method.AppContext.InstructionSet is InstructionSets.NewArmV8InstructionSet
            && method.AppContext.UnityVersion.Major == 2018 && method.AppContext.UnityVersion.Minor == 4
            && method.AppContext.Binary.PointerSizeBytes == 8 ? Recover(method) : 0;

    public static int Recover(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph) return 0;
        var changes = 0;
        foreach (var depth in graph.Blocks.ToArray())
        {
            if (!graph.Blocks.Contains(depth) || depth.Successors.Count != 2
                || depth.Successors.Distinct().Count() != 2
                || depth.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump } jump) continue;
            var resolver = new Resolver(method);
            var test = resolver.Predicate(jump.Operands[1], jump);
            if (test is not { Definition.OpCode: OpCode.CheckLess or OpCode.CheckGreaterOrEqual } predicate
                || predicate.Definition.Operands.Count != 3) continue;
            var first = resolver.Value(predicate.Definition.Operands[1], predicate.Definition);
            var second = resolver.Value(predicate.Definition.Operands[2], predicate.Definition);
            if (first is not { Kind: "depth", A.Kind: "object-class", A.Object: { } source }
                || second is not { Kind: "depth", A.Kind: "type", A.Type: { } target }
                || !OrdinaryClass(target) || !resolver.NonNull(source, depth)) continue;
            var failure = (predicate.Definition.OpCode == OpCode.CheckLess) != predicate.Inverted
                ? jump.Operands[0] as Block : depth.Successors.Single(b => !ReferenceEquals(b, jump.Operands[0]));
            if (failure == null || !depth.Successors.Contains(failure)) continue;
            var ancestor = depth.Successors.Single(b => !ReferenceEquals(b, failure));
            if (ancestor.Predecessors.Count != 1 || !ReferenceEquals(ancestor.Predecessors[0], depth)
                || ancestor.Successors.Count != 2 || ancestor.Successors.Distinct().Count() != 2
                || !ancestor.Successors.Contains(failure)
                || ancestor.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump } branch) continue;
            var equality = resolver.Predicate(branch.Operands[1], branch);
            if (equality is not { Definition.OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual } equal
                || equal.Definition.Operands.Count != 3) continue;
            var slot = resolver.Value(equal.Definition.Operands[1], equal.Definition);
            var expected = resolver.Value(equal.Definition.Operands[2], equal.Definition);
            if (slot is not { Kind: "ancestor", A: { } actualClass, Type: { } slotType }
                || !Same(actualClass, first.A) || !ReferenceEquals(slotType, target)
                || expected is not { Kind: "type", Type: { } expectedType }
                || !ReferenceEquals(expectedType, target)) continue;
            var success = (equal.Definition.OpCode == OpCode.CheckEqual) != equal.Inverted
                ? branch.Operands[0] as Block : ancestor.Successors.Single(b => !ReferenceEquals(b, branch.Operands[0]));
            if (success == null || ReferenceEquals(success, failure) || !ancestor.Successors.Contains(success)
                || !PureAncestor(ancestor, resolver) || !PreservedEscapes(graph, depth, ancestor, resolver)) continue;

            var result = new LocalVariable("shared_isinst_" + depth.ID, new(null, "shared_isinst_" + depth.ID), target);
            var flag = new LocalVariable("shared_isinst_null_" + depth.ID, new(null, "shared_isinst_null_" + depth.ID),
                method.AppContext.SystemTypes.SystemBooleanType);
            method.Locals.Add(result); method.Locals.Add(flag);
            depth.Instructions.RemoveAt(depth.Instructions.Count - 1);
            depth.Instructions.Add(new(jump.Index, OpCode.IsInst, result, target, source));
            depth.Instructions.Add(new(jump.Index, OpCode.CheckEqual, flag, result, new Immediate(0)));
            depth.Instructions.Add(new(jump.Index, OpCode.ConditionalJump, failure, flag));
            graph.RemoveEdge(depth, ancestor);
            graph.RemoveEdge(ancestor, success); graph.RemoveEdge(ancestor, failure);
            depth.Successors.Insert(0, success); success.Predecessors.Add(depth);
            graph.RemoveUnreachableBlocks(); depth.CalculateBlockType(); changes++;
        }
        if (changes > 0) DeadCodeEliminator.Run(method);
        return changes;
    }

    private static bool OrdinaryClass(TypeAnalysisContext type)
        => !type.IsValueType && !type.IsInterface && type is not GenericParameterTypeAnalysisContext
            && type.Type is LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_CLASS
                or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_STRING
                or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;

    private sealed record Expr(string Kind, LocalVariable? Object = null, TypeAnalysisContext? Type = null, Expr? A = null);
    private static bool Same(Expr? a, Expr? b)
        => a != null && b != null && a.Kind == b.Kind && ReferenceEquals(a.Object, b.Object)
            && ReferenceEquals(a.Type, b.Type) && (a.A == null ? b.A == null : Same(a.A, b.A));

    private static bool PureAncestor(Block block, Resolver resolver)
    {
        foreach (var instruction in block.Instructions)
        {
            if (instruction.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.Add or OpCode.ShiftLeft
                or OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.Not or OpCode.ConditionalJump)) return false;
            if (instruction.Destination is MemoryOperand or FieldReference || instruction.ImplicitDefinition != null) return false;
            if (instruction.OpCode == OpCode.Move && instruction.Operands.Count == 2
                && instruction.Operands[1] is MemoryOperand memory)
            {
                var value = resolver.Memory(memory, instruction);
                if (value == null || value.Kind is not ("object-class" or "depth" or "table" or "ancestor")) return false;
            }
            if (instruction.Operands.Any(o => o is FieldReference or AddressOf or ArrayAccess or ArrayLength)) return false;
        }
        return true;
    }

    private static bool Contains(IOperand value, LocalVariable local) => value switch
    {
        LocalVariable found => ReferenceEquals(found, local),
        MemoryOperand m => m.Base != null && Contains(m.Base, local) || m.Index != null && Contains(m.Index, local),
        FieldReference f => ReferenceEquals(f.Local, local) || f.Parent != null && Contains(f.Parent, local),
        AddressOf a => Contains(a.Target, local), ArrayAccess a => ReferenceEquals(a.Array, local) || Contains(a.Index, local),
        ArrayLength a => ReferenceEquals(a.Array, local), _ => false
    };

    private static bool PreservedEscapes(ISILControlFlowGraph graph, Block depth, Block ancestor, Resolver resolver)
    {
        foreach (var local in ancestor.Instructions.Select(i => i.Destination).OfType<LocalVariable>().Distinct())
        {
            var externalRead = graph.Blocks.Where(b => !ReferenceEquals(b, ancestor)).SelectMany(b => b.Instructions)
                .Any(i => i.Operands.Any(o => !(o is LocalVariable && ReferenceEquals(o, i.Destination)) && Contains(o, local)));
            if (!externalRead) continue;
            var writes = ancestor.Instructions.Where(i => ReferenceEquals(i.Destination, local)).ToArray();
            var previous = depth.Instructions.LastOrDefault(i => ReferenceEquals(i.Destination, local));
            if (writes is not [Instruction { OpCode: OpCode.Move, Operands: [_, LocalVariable oldSource] } copy]
                || previous is not { OpCode: OpCode.Move, Operands: [_, LocalVariable beforeSource] }
                || !Same(resolver.Value(beforeSource, previous), resolver.Value(oldSource, copy))) return false;
        }
        return true;
    }

    private sealed class Resolver(MethodAnalysisContext method)
    {
        private readonly ISILControlFlowGraph _graph = method.ControlFlowGraph!;
        private readonly HashSet<(LocalVariable, Instruction)> _active = [];
        private readonly Dictionary<(LocalVariable, Instruction), Expr?> _memo = [];
        public sealed record Test(Instruction Definition, bool Inverted);

        private static bool Barrier(Instruction i) => i.IsCall || i.OpCode is OpCode.IndirectCall or OpCode.Newobj or OpCode.CastClass
            || i.Destination is MemoryOperand or FieldReference || i.ImplicitDefinition != null;

        private List<Instruction>? Definitions(LocalVariable local, Instruction use)
        {
            var blocks = _graph.Blocks.Where(b => b.Instructions.Contains(use)).ToArray();
            if (blocks.Length != 1) return null;
            var definitions = new List<Instruction>(); var active = new HashSet<Block>(); var visits = 0;
            bool Walk(Block block, int before)
            {
                if (++visits > 512 || !active.Add(block)) return false;
                for (var index = before - 1; index >= 0; index--)
                {
                    var instruction = block.Instructions[index];
                    if (ReferenceEquals(instruction.Destination, local))
                    {
                        definitions.Add(instruction); active.Remove(block); return true;
                    }
                    if (Barrier(instruction)) { active.Remove(block); return false; }
                }
                if (block.Predecessors.Count == 0) { active.Remove(block); return false; }
                foreach (var predecessor in block.Predecessors)
                    if (!Walk(predecessor, predecessor.Instructions.Count)) { active.Remove(block); return false; }
                active.Remove(block); return true;
            }
            return Walk(blocks[0], blocks[0].Instructions.IndexOf(use)) ? definitions.Distinct().ToList() : null;
        }

        public Test? Predicate(IOperand value, Instruction use, int budget = 0)
        {
            if (budget > 32 || value is not LocalVariable { Type.FullName: "System.Boolean" } local) return null;
            var defs = Definitions(local, use);
            if (defs is not [var definition]) return null;
            if (definition is { OpCode: OpCode.Move, Operands: [_, var source] }) return Predicate(source, definition, budget + 1);
            if (definition is { OpCode: OpCode.Not, Operands: [_, var inverted] })
            {
                var test = Predicate(inverted, definition, budget + 1);
                return test == null ? null : new(test.Definition, !test.Inverted);
            }
            return new(definition, false);
        }

        private LocalVariable? Reference(IOperand value, Instruction use, int budget = 0)
        {
            if (budget > 32 || value is not LocalVariable { Type: { } type } local
                || !NullBypassRuntimeCastRecovery.ReferenceType(type)) return null;
            var block = _graph.Blocks.Single(b => b.Instructions.Contains(use));
            if (!InlineClassTestRecovery.StableSource(method, local, block)) return null;
            var writes = _graph.Instructions.Where(i => ReferenceEquals(i.Destination, local)).ToArray();
            if (writes is [Instruction { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] } copy]
                && copy.NativeRegisterCopySize is 0 or 8)
                return Reference(copied, copy, budget + 1);
            return local;
        }

        public Expr? Value(IOperand value, Instruction use, int budget = 0)
        {
            if (budget > 64) return null;
            if (value is TypeAnalysisContext type and not (RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext)) return new("type", Type: type);
            if (value is not LocalVariable local) return null;
            if (Reference(local, use) is { } reference) return new("reference", Object: reference);
            var key = (local, use);
            if (_memo.TryGetValue(key, out var cached)) return cached;
            if (!_active.Add(key)) return null;
            var definitions = Definitions(local, use); Expr? result = null;
            if (definitions is { Count: >0 })
                foreach (var definition in definitions)
                {
                    var candidate = Definition(definition, budget + 1);
                    if (candidate == null || result != null && !Same(candidate, result)) { result = null; break; }
                    result = candidate;
                }
            _active.Remove(key); _memo[key] = result; return result;
        }

        private Expr? Definition(Instruction instruction, int budget)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] }) return Memory(memory, instruction, budget);
            if (instruction is { OpCode: OpCode.Move, Operands: [_, var source] }
                && instruction.NativeRegisterCopySize is 0 or 8) return Value(source, instruction, budget);
            if (instruction is { OpCode: OpCode.ShiftLeft, Operands: [_, var amount, Immediate { Value: 3 }] }
                && Value(amount, instruction, budget) is { Kind: "depth", A.Kind: "type", A.Type: { } target })
                return new("shifted-depth", Type: target);
            if (instruction is { OpCode: OpCode.Add, Operands: [_, var table, var index] }
                && Value(table, instruction, budget) is { Kind: "table", A.Kind: "object-class" } hierarchy
                && Value(index, instruction, budget) is { Kind: "shifted-depth", Type: { } slotType })
                return new("slot-address", Type: slotType, A: hierarchy.A);
            return null;
        }

        public Expr? Memory(MemoryOperand memory, Instruction use, int budget = 0)
        {
            if (budget > 64 || memory.Index != null || memory.Scale != 0 || memory.Base == null) return null;
            var root = Value(memory.Base, use, budget + 1);
            if (memory.Addend == 0 && use.NativeReadSize == 8 && root is { Kind: "reference", Object: { } obj })
                return new("object-class", Object: obj);
            if (memory.Addend == 0x120 && use.NativeReadSize == 1 && root is { Kind: "object-class" or "type" })
                return new("depth", A: root);
            if (memory.Addend == 0xC8 && use.NativeReadSize == 8 && root is { Kind: "object-class" })
                return new("table", A: root);
            if (memory.Addend == -8 && use.NativeReadSize == 8 && root is { Kind: "slot-address", Type: { } target })
                return new("ancestor", Type: target, A: root.A);
            return null;
        }

        public bool NonNull(LocalVariable source, Block consumer)
        {
            var dominance = new DominatorInfo(_graph);
            foreach (var guard in _graph.Blocks)
            {
                if (guard.Successors.Count != 2 || guard.Successors.Distinct().Count() != 2
                    || !dominance.Dominates(guard, consumer)
                    || guard.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump } jump) continue;
                var predicate = Predicate(jump.Operands[1], jump);
                if (predicate is not { Definition.OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual } test
                    || test.Definition.Operands.Count != 3) continue;
                var first = test.Definition.Operands[1]; var second = test.Definition.Operands[2];
                var input = second is Immediate { Value: 0 } ? first : first is Immediate { Value: 0 } ? second : null;
                if (input == null || !ReferenceEquals(Reference(input, test.Definition), source)) continue;
                var branch = jump.Operands[0] as Block;
                if (branch == null || !guard.Successors.Contains(branch)) continue;
                var nullTarget = (test.Definition.OpCode == OpCode.CheckEqual) != test.Inverted
                    ? branch : guard.Successors.Single(b => !ReferenceEquals(b, branch));
                var nonnull = guard.Successors.Single(b => !ReferenceEquals(b, nullTarget));
                if (dominance.Dominates(nonnull, consumer)) return true;
            }
            return false;
        }
    }
}
