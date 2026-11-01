using System;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete original XmlElementWrapper.SetAttributeNode (0xE9D238) keeps the
// class load in the non-null guard while its automatic exception path only
// loads the class name. Keep the original null bypass and all shared success
// paths. Never infer non-nullness from an earlier cast or static type alone.
public static class DominatedRuntimeCastRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph || !CheckedUnboxRecovery.Supports(method.AppContext)) return 0;
        var count = 0;
        foreach (var block in graph.Blocks.ToArray())
            if (graph.Blocks.Contains(block) && TryRecover(method, block,
                address => InlineClassCastRecovery.IsMessageBuilder(method, address))) count++;
        if (count > 0) { graph.RemoveUnreachableBlocks(); DeadCodeEliminator.Run(method); }
        return count;
    }

    internal static bool TryRecover(MethodAnalysisContext method, Block guard, Func<ulong, bool> helper)
    {
        if (method.ControlFlowGraph is not { } graph) return false;
        var check = guard.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        Instruction? classLoad = null;
        if (check.FirstOrDefault() is { OpCode: OpCode.Move, NativeReadSize: 8,
            Operands: [LocalVariable, MemoryOperand { Addend: 0, Index: null, Scale: 0 }] } load)
        { classLoad = load; check = check[1..]; }
        Instruction? inversion = null;
        if (check is [_, _, Instruction { OpCode: OpCode.Not } invert, _])
        { inversion = invert; check = [check[0], check[1], check[3]]; }
        if (check is not [Instruction { OpCode: OpCode.IsInst,
                Operands: [LocalVariable result, TypeAnalysisContext target, LocalVariable source] } cast,
            Instruction { OpCode: OpCode.CheckEqual, Operands: [LocalVariable flag, var tested, Immediate { Value: 0 }] },
            Instruction { OpCode: OpCode.ConditionalJump, Operands: [Block branch, LocalVariable condition] }]
            || !ReferenceEquals(tested, result) || flag.Type?.FullName != "System.Boolean"
            || source.Type == null || !NullBypassRuntimeCastRecovery.ReferenceType(source.Type)
            || !NullBypassRuntimeCastRecovery.ReferenceType(target)
            || guard.Successors.Count != 2 || guard.Successors.Distinct().Count() != 2
            || !guard.Successors.Contains(branch) || ReferenceEquals(result, source)
            || method.ParameterLocals.Contains(result)
            || graph.Instructions.Count(i => ReferenceEquals(i.Destination, result)) != 1
            || !DominatingReferenceGuardProof.NonNullAt(method, source, guard)) return false;
        if (inversion == null && !ReferenceEquals(condition, flag)) return false;
        if (inversion != null && (inversion.Operands is not [LocalVariable notFlag, var operand]
                || notFlag.Type?.FullName != "System.Boolean" || !ReferenceEquals(operand, flag)
                || !ReferenceEquals(condition, notFlag))) return false;
        var other = guard.Successors.Single(b => !ReferenceEquals(b, branch));
        var failure = inversion == null ? branch : other;
        var success = inversion == null ? other : branch;
        if (failure.Predecessors.Count != 1 || !ReferenceEquals(failure.Predecessors[0], guard)) return false;
        var body = failure.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (classLoad == null)
        {
            if (body.FirstOrDefault() is not { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [LocalVariable, MemoryOperand { Addend: 0, Index: null, Scale: 0 }] } loadInFailure) return false;
            classLoad = loadInFailure; body = body[1..];
        }
        if (classLoad.Operands is not [LocalVariable klass, MemoryOperand { Base: var obj }]
            || !ReferenceEquals(obj, source)
            || body is not [Instruction { OpCode: OpCode.Move, NativeReadSize: 8,
                    Operands: [LocalVariable name, MemoryOperand { Base: var classBase, Addend: 0x40, Index: null, Scale: 0 }] },
                Instruction { OpCode: OpCode.Call, Operands: [Immediate { Value: >= 0 } address,
                    LocalVariable message, var fromClass, var toClass] },
                Instruction { OpCode: OpCode.Newobj, Operands: [LocalVariable exception,
                    TypeAnalysisContext { FullName: "System.InvalidCastException" }] }]
            || !ReferenceEquals(classBase, klass) || !ReferenceEquals(fromClass, name)
            || !helper((ulong)address.Value) || failure.Successors.Count != 1) return false;
        var represented = toClass is RuntimeClassTypeAnalysisContext runtime ? runtime.RepresentedType : toClass as TypeAnalysisContext;
        if (represented == null || !NullBypassRuntimeCastRecovery.SameCastType(represented, target)) return false;
        var transport = failure.Successors[0];
        if (transport.Predecessors.Count != 1 || !ReferenceEquals(transport.Predecessors[0], failure)
            || transport.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray() is not
                [Instruction { OpCode: OpCode.Throw, Operands: [var thrown] }]
            || !ReferenceEquals(thrown, exception) || transport.Successors.Count != 1
            || !ReferenceEquals(transport.Successors[0], graph.ExitBlock)) return false;
        var removed = new[] { klass, name, message, exception, flag }
            .Concat(inversion == null ? Array.Empty<LocalVariable>() : new[] { (LocalVariable)inversion.Operands[0] }).ToArray();
        if (removed.Distinct().Count() != removed.Length || removed.Contains(source) || removed.Contains(result)
            || removed.Any(local => method.ParameterLocals.Contains(local)
                || graph.Instructions.Count(i => ReferenceEquals(i.Destination, local)) != 1)
            || graph.Blocks.Where(b => !ReferenceEquals(b, guard) && !ReferenceEquals(b, failure) && !ReferenceEquals(b, transport))
                .SelectMany(b => b.Instructions).SelectMany(i => i.Operands)
                .Any(o => removed.Any(local => RuntimeCheckedCastRecovery.Contains(o, local)))) return false;
        // All rejection paths above are read-only. The original null edge and
        // continuation instructions remain untouched, including unrelated calls.
        cast.OpCode = OpCode.CastClass;
        guard.Instructions = [cast, new(check[^1].Index, OpCode.Jump, success)];
        graph.RemoveEdge(guard, failure); guard.CalculateBlockType();
        return true;
    }
}
