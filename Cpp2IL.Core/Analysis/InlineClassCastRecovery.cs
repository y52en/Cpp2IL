using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recognized offsets are the inspected Unity 2018.4 ARM64 profile.
// Rewrites require an additional null bypass and hash-proven exception transport.
public static class InlineClassCastRecovery
{
    public record Match(Block Depth, Block Ancestor, Block Failure, Block Success,
                        IOperand Object, TypeAnalysisContext Target);

    // Complete native helper body inspected with Ghidra in the matching unpacked image.
    // Fingerprint, not an address/name heuristic: unrelated builds remain unsupported.
    private const string MessageBuilderHash = "d8069611fda0fda396f673b72c5b87b3d1a03cd2615a82b260da93466875bf4f";
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, bool>> Helpers = new();

    internal static bool IsMessageBuilder(MethodAnalysisContext method, ulong address)
        => Helpers.GetValue(method.AppContext, _ => new()).GetOrAdd(address, candidate =>
        {
            try
            {
                var binary = method.AppContext.Binary;
                var offset = checked((int)binary.MapVirtualAddressToRaw(candidate));
                var content = binary.GetRawBinaryContent();
                if (offset < 0 || offset > content.Length - 0xB8) return false;
                using var sha = SHA256.Create();
                var hash = sha.ComputeHash(content.Slice(offset, 0xB8).ToArray());
                return string.Concat(hash.Select(b => b.ToString("x2"))) == MessageBuilderHash;
            }
            catch (Exception) { return false; }
        });

    private static IOperand Resolve(IOperand value, IReadOnlyDictionary<LocalVariable, Instruction> defs)
    {
        var seen = new HashSet<LocalVariable>();
        while (value is LocalVariable local && seen.Add(local) && defs.TryGetValue(local, out var instruction)
               && instruction is { OpCode: OpCode.Move, Operands: [_, var source] }) value = source;
        return value;
    }

    internal static bool HasNullBypass(Match match, IReadOnlyDictionary<LocalVariable, Instruction> defs)
    {
        if (match.Depth.Predecessors.Count != 1) return false;
        var guard = match.Depth.Predecessors[0];
        if (guard.Successors.Count != 2 || guard.Instructions.LastOrDefault() is not
            { OpCode: OpCode.ConditionalJump, Operands: [Block target, var condition] }) return false;
        if (!guard.Successors.Contains(target)) return false;
        var inverted = false;
        var seen = new HashSet<LocalVariable>();
        condition = Resolve(condition, defs);
        while (condition is LocalVariable flag && seen.Add(flag) && defs.TryGetValue(flag, out var definition))
        {
            if (definition is { OpCode: OpCode.Not, Operands: [_, LocalVariable operand] }
                && flag.Type?.FullName == "System.Boolean" && operand.Type?.FullName == "System.Boolean")
            { inverted = !inverted; condition = Resolve(operand, defs); continue; }
            if (definition.Operands is not [_, var first, var second]
                || definition.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)) return false;
            var obj = Resolve(match.Object, defs);
            var comparesNull = (Resolve(first, defs) is Immediate { Value: 0 } && ReferenceEquals(Resolve(second, defs), obj))
                || (Resolve(second, defs) is Immediate { Value: 0 } && ReferenceEquals(Resolve(first, defs), obj));
            var jumpsOnNull = (definition.OpCode == OpCode.CheckEqual) != inverted;
            return comparesNull && (jumpsOnNull != ReferenceEquals(target, match.Depth));
        }
        return false;
    }

    private static HashSet<Block>? ExceptionTransport(MethodAnalysisContext method, Match match,
        IReadOnlyDictionary<LocalVariable, Instruction> defs)
    {
        if (match.Failure.Predecessors.Count != 2 || !match.Failure.Predecessors.Contains(match.Depth)
            || !match.Failure.Predecessors.Contains(match.Ancestor)) return null;
        var region = new HashSet<Block>();
        var current = match.Failure;
        LocalVariable? exception = null;
        var builderSeen = false;
        while (region.Add(current))
        {
            foreach (var instruction in current.Instructions)
            {
                if (instruction.OpCode == OpCode.Nop) continue;
                if (instruction is { OpCode: OpCode.Move, Destination: LocalVariable }) continue;
                if (!builderSeen && instruction is
                    { OpCode: OpCode.Call, Operands: [Immediate address, _, var name, var target, ..] }
                    && address.Value >= 0 && IsMessageBuilder(method, (ulong)address.Value)
                    && Resolve(name, defs) is MemoryOperand { Addend: 0x40, Index: null, Scale: 0, Base: { } klass }
                    && Resolve(klass, defs) is MemoryOperand { Addend: 0, Index: null, Scale: 0, Base: { } obj }
                    && ReferenceEquals(Resolve(obj, defs), Resolve(match.Object, defs))
                    && ReferenceEquals(Resolve(target, defs), match.Target))
                { builderSeen = true; continue; }
                if (builderSeen && exception == null && instruction is
                    { OpCode: OpCode.Newobj, Operands: [LocalVariable created, TypeAnalysisContext type] }
                    && type.FullName == "System.InvalidCastException") { exception = created; continue; }
                if (instruction is { OpCode: OpCode.Throw, Operands: [var thrown] }
                    && exception != null && ReferenceEquals(Resolve(thrown, defs), exception)
                    && ReferenceEquals(instruction, current.Instructions.Last())
                    && current.Successors.Count == 1 && ReferenceEquals(current.Successors[0], method.ControlFlowGraph!.ExitBlock))
                    return region;
                // Includes calls, stores, branches, explicit messages and cleanup: never erase them.
                return null;
            }
            if (current.Successors.Count != 1) return null;
            var next = current.Successors[0];
            if (next.Predecessors.Count != 1 || !ReferenceEquals(next.Predecessors[0], current)) return null;
            current = next;
        }
        return null;
    }

    internal static IOperand Replace(IOperand operand, LocalVariable source, LocalVariable result) => operand switch
    {
        LocalVariable local when ReferenceEquals(local, source) => result,
        MemoryOperand memory => new MemoryOperand(memory.Base == null ? null : Replace(memory.Base, source, result),
            memory.Index == null ? null : Replace(memory.Index, source, result), memory.Addend, memory.Scale),
        FieldReference field => new FieldReference(field.Field,
            ReferenceEquals(field.Local, source) ? result : field.Local, field.Offset)
            { Parent = field.Parent == null ? null : (FieldReference)Replace(field.Parent, source, result) },
        AddressOf address => new AddressOf(Replace(address.Target, source, result)),
        ArrayAccess access => new ArrayAccess(ReferenceEquals(access.Array, source) ? result : access.Array, Replace(access.Index, source, result)),
        ArrayLength length => new ArrayLength(ReferenceEquals(length.Array, source) ? result : length.Array),
        _ => operand
    };

    private static bool Contains(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable candidate => ReferenceEquals(candidate, local),
        MemoryOperand memory => (memory.Base != null && Contains(memory.Base, local))
            || (memory.Index != null && Contains(memory.Index, local)),
        FieldReference field => ReferenceEquals(field.Local, local) || (field.Parent != null && Contains(field.Parent, local)),
        AddressOf address => Contains(address.Target, local),
        ArrayAccess access => ReferenceEquals(access.Array, local) || Contains(access.Index, local),
        ArrayLength length => ReferenceEquals(length.Array, local),
        _ => false
    };

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.ControlFlowGraph == null) return 0;
        var cfg = method.ControlFlowGraph;
        DeadCodeEliminator.Run(cfg);
        var trace = Environment.GetEnvironmentVariable("CPP2IL_TRACE_CAST_RVA") == method.UnderlyingPointer.ToString("X");
        if (trace) foreach (var block in cfg.Blocks) Console.WriteLine("CAST_STAGE " + block);
        var changes = 0;
        foreach (var depth in cfg.Blocks.ToArray())
        {
            if (!cfg.Blocks.Contains(depth)) continue;
            var defs = cfg.Blocks.SelectMany(b => b.Instructions).Where(i => i.Destination is LocalVariable)
                .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            var match = TryMatch(depth, defs);
            if (trace && match != null) Console.WriteLine($"CAST_MATCH {depth.ID} null={HasNullBypass(match, defs)} successPreds={match.Success.Predecessors.Count}");
            if (match?.Object is not LocalVariable source
                || !(defs.ContainsKey(source) || method.ParameterLocals.Contains(source)
                    && source.Type is {IsValueType:false}
                    && source.Type is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext)
                    && method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
                    && InlineClassTestRecovery.PureKernel(match))
                || !HasNullBypass(match, defs)
                || match.Success.Instructions.Any(i => i.OpCode == OpCode.Phi)) continue;
            var insertion=InlineClassTestRecovery.CheckInsertionBlock(method,match,source);
            if(insertion==null)continue;
            var transport = ExceptionTransport(method, match, defs);
            if (trace) Console.WriteLine($"CAST_TRANSPORT {depth.ID} proven={transport != null}");
            if (transport == null) continue;
            // Avoid losing SSA values whose definitions would disappear with the lookup/throw path.
            var removed = new HashSet<Block>(transport) { match.Ancestor };
            var locals = removed.SelectMany(b => b.Instructions).Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
            if (cfg.Blocks.Where(b => !removed.Contains(b)).SelectMany(b => b.Instructions)
                .SelectMany(i => i.Operands).Any(o => locals.Any(l => Contains(o, l)))) continue;

            // Only substitute uses on paths dominated by success; null bypasses and other phi inputs stay unchanged.
            var bypassReachable = new HashSet<Block>();
            var queue = new Queue<Block>(); queue.Enqueue(cfg.EntryBlock);
            while (queue.Count != 0)
            {
                var block = queue.Dequeue();
                if (ReferenceEquals(block, match.Success) || !bypassReachable.Add(block)) continue;
                foreach (var successor in block.Successors) queue.Enqueue(successor);
            }
            var result = new LocalVariable("cast_" + depth.ID, new Register(null, "cast_" + depth.ID), match.Target);
            method.Locals.Add(result);
            insertion.Instructions.Insert(insertion.Instructions.Count - 1,
                new Instruction(depth.Instructions.Last().Index, OpCode.CastClass, result, match.Target, source));
            depth.Instructions.Last().OpCode = OpCode.Jump;
            depth.Instructions.Last().SetOperands(match.Success);
            cfg.RemoveEdge(depth, match.Failure);
            cfg.RemoveEdge(depth, match.Ancestor);
            cfg.RemoveEdge(match.Ancestor, match.Success);
            depth.Successors.Add(match.Success); match.Success.Predecessors.Add(depth);
            cfg.RemoveUnreachableBlocks();
            foreach (var block in cfg.Blocks.Where(b => !bypassReachable.Contains(b)))
                foreach (var instruction in block.Instructions)
                    for (var i = 0; i < instruction.Operands.Count; i++)
                    {
                        if (instruction.Operands[i] is LocalVariable local && ReferenceEquals(local, instruction.Destination)) continue;
                        if (instruction.OpCode == OpCode.Phi && (i == 0 || bypassReachable.Contains(block.Predecessors[i - 1]))) continue;
                        instruction.SetOperand(i, Replace(instruction.Operands[i], source, result));
                    }
            depth.CalculateBlockType();
            changes++;
        }
        if (changes != 0)
        {
            // Cast-derived receiver types become known only in this late pass.
            // Resolve their native field offsets before IL emission, including
            // stores: an unresolved destination must never silently lose a write.
            MetadataResolver.ResolveFieldOffsets(method);
            DeadCodeEliminator.Run(cfg);
        }
        return changes;
    }

    public static Match? TryMatch(Block depth, IReadOnlyDictionary<LocalVariable, Instruction> defs)
    {
        IOperand Resolve(IOperand value)
        {
            var seen=new HashSet<LocalVariable>();
            while (value is LocalVariable local && seen.Add(local)
                   && defs.TryGetValue(local,out var definition)
                   && definition is { OpCode: OpCode.Move, Operands: [_, var source] }) value=source;
            return value;
        }
        Instruction? Predicate(IOperand value, out bool inverted)
        {
            inverted=false;var seen=new HashSet<LocalVariable>();
            while (value is LocalVariable local && seen.Add(local) && defs.TryGetValue(local,out var definition))
            {
                if (definition is { OpCode: OpCode.Move, Operands: [_, var source] }) { value=source;continue; }
                if (definition is { OpCode: OpCode.Not, Operands: [_, LocalVariable operand] }
                    && local.Type?.FullName=="System.Boolean" && operand.Type?.FullName=="System.Boolean")
                { inverted=!inverted;value=operand;continue; }
                return definition;
            }
            return null;
        }
        TypeAnalysisContext? Class(IOperand value) => value switch
        {
            LocalVariable { Type: RuntimeClassTypeAnalysisContext runtime } => runtime.RepresentedType,
            RuntimeClassTypeAnalysisContext runtime => runtime.RepresentedType,
            TypeAnalysisContext type when type is not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext) => type,
            _ => null
        };
        if (depth.Successors.Count!=2 || depth.Instructions.LastOrDefault() is not
            { OpCode: OpCode.ConditionalJump, Operands: [Block depthTarget, var condition] }) return null;
        if (!depth.Successors.Contains(depthTarget) || depth.Successors.Distinct().Count()!=2) return null;
        var comparison=Predicate(condition,out var inverted);
        if (comparison is not { OpCode:OpCode.CheckLess or OpCode.CheckGreaterOrEqual, Operands: [_, var first, var second] }) return null;
        var failure=(comparison.OpCode==OpCode.CheckLess)!=inverted ?depthTarget
            :depth.Successors.Single(b=>!ReferenceEquals(b,depthTarget));
        if (Resolve(first) is not MemoryOperand { Addend: 0x120, Index: null, Scale: 0, Base: { } sourceClass }
            || Resolve(second) is not MemoryOperand { Addend: 0x120, Index: null, Scale: 0, Base: { } targetClass }) return null;
        var target=Class(targetClass) ?? Class(Resolve(targetClass));
        if (target==null || target.IsValueType || target.IsInterface || Class(sourceClass)==null) return null;
        if (Resolve(sourceClass) is not MemoryOperand { Addend: 0, Index: null, Scale: 0, Base: { } sourceObject }) return null;
        var ancestor=depth.Successors.SingleOrDefault(b=>!ReferenceEquals(b,failure));
        if (ancestor==null || ancestor.Predecessors.Count!=1 || !ReferenceEquals(ancestor.Predecessors[0],depth)
            || ancestor.Successors.Count!=2 || !ancestor.Successors.Contains(failure)) return null;
        if (ancestor.Instructions.LastOrDefault() is not
            { OpCode: OpCode.ConditionalJump, Operands: [Block ancestorTarget, var ancestorCondition] }
            || !ancestor.Successors.Contains(ancestorTarget) || ancestor.Successors.Distinct().Count()!=2) return null;
        var equality=Predicate(ancestorCondition,out inverted);
        if (equality is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var slot, var expected] }) return null;
        var success=(equality.OpCode==OpCode.CheckEqual)!=inverted ?ancestorTarget
            :ancestor.Successors.Single(b=>!ReferenceEquals(b,ancestorTarget));
        if(ReferenceEquals(success,failure))return null;
        if (!ReferenceEquals(Class(expected) ?? Class(Resolve(expected)),target)) return null;
        if (Resolve(slot) is not MemoryOperand { Addend: -8, Index: null, Scale: 0, Base: LocalVariable address }
            || !defs.TryGetValue(address,out var add)
            || add is not { OpCode: OpCode.Add, Operands: [_, var table, LocalVariable index] }) return null;
        if (Resolve(table) is not MemoryOperand { Addend: 0xC8, Index: null, Scale: 0, Base: { } tableClass }
            || !ReferenceEquals(Resolve(tableClass),Resolve(sourceClass))) return null;
        if (!defs.TryGetValue(index,out var shift)
            || shift is not { OpCode: OpCode.ShiftLeft, Operands: [_, var targetDepth, Immediate { Value: 3 }] }
            || Resolve(targetDepth) is not MemoryOperand { Addend: 0x120, Index: null, Scale: 0, Base: { } shiftedClass }
            || !ReferenceEquals(Class(shiftedClass) ?? Class(Resolve(shiftedClass)),target)) return null;
        // Never classify a lookup with calls/stores/custom effects as an inline type test.
        if (ancestor.Instructions.Any(i=>i.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.Add or OpCode.Subtract
            or OpCode.ShiftLeft or OpCode.Xor or OpCode.And or OpCode.Or or OpCode.Not
            or OpCode.CheckEqual or OpCode.CheckLess or OpCode.CheckGreater or OpCode.CheckNotEqual
            or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual or OpCode.ConditionalJump))) return null;
        if (ancestor.Instructions.Any(i=>i.Destination is MemoryOperand or FieldReference)) return null;
        return new(depth,ancestor,failure,success,sourceObject,target);
    }
}
