using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// SSA reference provenance for one already-proven typed atomic location.
// A base-class spelling is insufficient: prove every Phi edge individually.
internal static class Arm64AtomicReferenceProof
{
    internal static bool Prove(MethodAnalysisContext method, Instruction atomic, IOperand operand, TypeAnalysisContext type)
    {
        if (!type.IsSealed || type.HasAnyGenericParameters() || !NullBypassRuntimeCastRecovery.ReferenceType(type)
            || method.ControlFlowGraph is not {} graph || atomic.Destination is not LocalVariable result) return false;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);
        var budget = 128;
        IOperand Root(IOperand value, Instruction use)
        {
            var visited = new HashSet<LocalVariable>();
            while (value is LocalVariable local && visited.Add(local) && visited.Count <= 16
                && definitions.TryGetValue(local, out var copy)
                && copy is { OpCode: OpCode.Move, NativeWriteSize: 0,
                    Operands: [_, LocalVariable or TypeAnalysisContext or Immediate] })
            {
                if (!ForwardNullCheckRecovery.DefinitionDominates(graph, copy, use)) break;
                var source = copy.Operands[1];
                if (source is not TypeAnalysisContext
                    && !(copy.NativeReadSize == 0 && (copy.NativeRegisterCopySize == 8
                        || copy.Index == -1 && copy.NativeRegisterCopySize == 0
                        || source is Immediate { Value: 0 } && copy.NativeZeroSize == 8))) break;
                value = source;
                use = copy;
            }
            return value;
        }
        bool Same(IOperand left, IOperand right, Instruction use) => ReferenceEquals(Root(left, use), Root(right, use));
        bool Target(IOperand value, Instruction use) => Root(value, use) switch
        {
            RuntimeClassTypeAnalysisContext runtime => TrivialConstructorRecovery.SameType(runtime.RepresentedType, type),
            TypeAnalysisContext target => TrivialConstructorRecovery.SameType(target, type),
            _ => false,
        };
        bool Guard(IOperand value, Block edge, Block successor)
        {
            if (edge.Successors.Count != 2 || edge.Successors.Distinct().Count() != 2
                || !edge.Successors.Contains(successor)
                || edge.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump,
                    Operands: [Block branch, var flag] } jump || !edge.Successors.Contains(branch)
                || Root(flag, jump) is not LocalVariable predicate
                || !definitions.TryGetValue(predicate, out var compare)
                || compare is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                    NativeComparisonSize: 8, Operands: [_, var a, var b] }
                || !edge.Instructions.Contains(compare)) return false;
            var equalityEdge = compare.OpCode == OpCode.CheckEqual
                ? branch : edge.Successors.Single(s => !ReferenceEquals(s, branch));
            if (!ReferenceEquals(equalityEdge, successor)) return false;
            if (Root(a, compare) is Immediate { Value: 0 } && Same(b, value, compare)
                || Root(b, compare) is Immediate { Value: 0 } && Same(a, value, compare)) return true;
            var klass = Target(a, compare) ? Root(b, compare) : Target(b, compare) ? Root(a, compare) : null;
            return klass is LocalVariable loaded && definitions.TryGetValue(loaded, out var load)
                && load is { OpCode: OpCode.Move, NativeReadSize: 8,
                    Operands: [_, MemoryOperand { Base: {} source, Index: null, Scale: 0, Addend: 0 }] }
                && Same(source, value, load)
                && ForwardNullCheckRecovery.DefinitionDominates(graph, load, compare);
        }
        bool Value(IOperand value, Instruction consumer, HashSet<LocalVariable> path)
        {
            if (--budget < 0) return false;
            if (value is Immediate { Value: 0 }) return true;
            if (value is not LocalVariable local) return false;
            if (TrivialConstructorRecovery.SameType(local.Type, type)) return true;
            if (!path.Add(local)) return false;
            try
            {
                if (!definitions.TryGetValue(local, out var definition) || definition == null
                    || !ForwardNullCheckRecovery.DefinitionDominates(graph, definition, consumer)) return false;
                // The observed old value has the managed location's type.
                // This anchor is usable only AFTER this call on a back edge,
                // never to justify a value read before its definition.
                if (ReferenceEquals(local, result)) return ReferenceEquals(definition, atomic);
                if (definition.OpCode == OpCode.Phi)
                {
                    var homes = graph.Blocks.Where(b => b.Instructions.Contains(definition)).ToArray();
                    if (homes.Length != 1) return false;
                    var home = homes[0];
                    if (home.Predecessors.Count == 0 || home.Predecessors.Distinct().Count() != home.Predecessors.Count
                        || definition.Operands.Count != home.Predecessors.Count + 1) return false;
                    for (var i = 0; i < home.Predecessors.Count; i++)
                    {
                        var edge = home.Predecessors[i]; var incoming = definition.Operands[i + 1];
                        if (!edge.Successors.Contains(home) || edge.Instructions.LastOrDefault() is not {} last
                            || !Guard(incoming, edge, home) && !Value(incoming, last, path)) return false;
                    }
                    return true;
                }
                if (definition is { OpCode: OpCode.CastClass or OpCode.IsInst,
                        Operands: [_, TypeAnalysisContext castType, _] }
                    && TrivialConstructorRecovery.SameType(castType, type)) return true;
                if (definition is { OpCode: OpCode.Call, Operands: [MethodAnalysisContext target, ..] }
                    && TrivialConstructorRecovery.SameType(target.ReturnType, type)) return true;
                if (definition is not { OpCode: OpCode.Move, Operands: [_, var source] }) return false;
                if (source is FieldReference field && definition.NativeReadSize == 8
                    && field.Parent == null && field.Offset == field.Field.DefaultOffset && field.Field.BackingData != null
                    && TrivialConstructorRecovery.SameType(field.Field.DefaultFieldType, type)
                    && TrivialConstructorRecovery.SameType(field.Field.FieldType, type)) return true;
                if (source is MemoryOperand { Base: {} address, Index: null, Scale: 0, Addend: 0 }
                    && definition.NativeReadSize == 8
                    && Arm64AtomicCompareExchangeRecovery.ResolveManagedAddress(method, definition, address)
                        is AddressOf { Target: FieldReference resolved }
                    && TrivialConstructorRecovery.SameType(resolved.Field.FieldType, type)) return true;
                return definition.NativeReadSize == 0 && definition.NativeWriteSize == 0
                    && (definition.NativeRegisterCopySize == 8
                        || definition.Index == -1 && definition.NativeRegisterCopySize == 0)
                    && Value(source, definition, path);
            }
            finally { path.Remove(local); }
        }
        return Value(operand, atomic, []);
    }
}
