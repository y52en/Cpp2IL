using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Copy and constant propagation, performed while the graph is still in SSA form.
/// </summary>
public static class SsaSimplifier
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!, method.ParameterLocals);

    public static void Run(ISILControlFlowGraph cfg, List<LocalVariable> parameterLocals)
    {
        // dest -> value for every forwardable copy/constant. SSA's single-assignment property means a
        // local is defined at most once, so there is never a conflicting entry for the same key.
        var forwarded = new Dictionary<LocalVariable, IOperand>();
        var mutableStructs = MutableStructStorage(cfg);
        var addressed = new HashSet<LocalVariable>();
        foreach(var instruction in cfg.Instructions)
            foreach(var operand in instruction.Operands)
                if(operand is AddressOf {Target:LocalVariable storage})addressed.Add(storage);
                else if(operand is AddressOf {Target:FieldReference fieldStorage}
                    && fieldStorage.RequiresReceiver && fieldStorage.Local.Type?.IsValueType==true)addressed.Add(fieldStorage.Local);
        var definitionCounts = cfg.Instructions.Select(i => i.Destination).OfType<LocalVariable>()
            .GroupBy(l => l).ToDictionary(g => g.Key, g => g.Count());

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is LocalVariable dest
                    && !parameterLocals.Contains(dest)
                    && definitionCounts.TryGetValue(dest,out var count) && count==1
                    // Addressed storage is memory, not a single-assignment
                    // value: a ref/out call can change it without a Move.
                    // Reading it captures a snapshot too; do not turn that
                    // copy into a live alias across a later ref/out call.
                    && !addressed.Contains(dest)
                    && !(instruction.Operands[1] is LocalVariable source && addressed.Contains(source))
                    && !PreserveStructCopy(dest, instruction.Operands[1], mutableStructs)
                    && IsForwardable(instruction.Operands[1]))
                    forwarded[dest] = instruction.Operands[1];

        // A join of the SAME integer/null bit constant is still that constant.
        // Include anchored self backedges, but never guess an unanchored cycle,
        // a mutable aggregate/storage slot, or a missing predecessor value.
        var phiChanged = true;
        while (phiChanged)
        {
            phiChanged = false;
            foreach (var block in cfg.Blocks)
            foreach (var phi in block.Instructions)
            {
                if (phi is not { OpCode: OpCode.Phi, Operands.Count: > 1 }
                    || phi.Operands[0] is not LocalVariable destination
                    || forwarded.ContainsKey(destination) || parameterLocals.Contains(destination)
                    || addressed.Contains(destination) || mutableStructs.Contains(destination) || IsStructStorage(destination)
                    || destination.Type?.FullName is "System.Single" or "System.Double"
                    || phi.Operands.Count != block.Predecessors.Count + 1
                    || !definitionCounts.TryGetValue(destination, out var writes) || writes != 1) continue;
                Immediate? constant = null;
                var valid = true;
                foreach (var input in phi.Operands.Skip(1))
                {
                    var value = input is LocalVariable local && forwarded.ContainsKey(local) ? Resolve(local, forwarded) : input;
                    if (ReferenceEquals(value, destination)) continue;
                    if (value is not Immediate immediate || constant is Immediate known && immediate.Value != known.Value)
                    { valid = false; break; }
                    constant ??= immediate;
                }
                if (!valid || constant == null) continue;
                forwarded[destination] = constant.Value;
                phiChanged = true;
            }
        }

        if (forwarded.Count == 0)
            return;

        // Collapse copy chains (t1 := a; t2 := t1; ...) so each local maps straight to its final value.
        var resolved = new Dictionary<LocalVariable, IOperand>();
        foreach (var dest in forwarded.Keys)
            resolved[dest] = Resolve(dest, forwarded);

        // One global substitution of every use.
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                ReplaceUses(instruction, resolved);

        // A forwarded local is dead now - unless a use could not take its value (a constant cannot be
        // a memory base/index, so such a use keeps the original local). Drop the defining Move only
        // once the local truly has no reads left; the leftover nops are cleared by SsaForm.Remove.
        var reads = CollectReadLocals(cfg);
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is LocalVariable dest
                    && forwarded.ContainsKey(dest)
                    && !reads.Contains(dest))
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                }
    }

    // Follows local-to-local copies to the end of the chain. The visited set guards against a cycle a
    // malformed graph could present; a well-formed SSA graph (definitions dominate uses) has none.
    private static IOperand Resolve(LocalVariable dest, Dictionary<LocalVariable, IOperand> forwarded)
    {
        var value = forwarded[dest];
        var visited = new HashSet<LocalVariable> { dest };

        while (value is LocalVariable next && forwarded.TryGetValue(next, out var nextValue) && visited.Add(next))
            value = nextValue;

        return value;
    }

    private static void ReplaceUses(Instruction instruction, Dictionary<LocalVariable, IOperand> resolved)
    {
        // The single definition position (a Move/Call destination local) must not be rewritten - only
        // reads are forwarded. In SSA the local being eliminated never appears as a use of itself, so
        // skipping just its own definition operand is sufficient.
        var destination = instruction.Destination;

        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            switch (instruction.Operands[i])
            {
                case LocalVariable local when !ReferenceEquals(local, destination) && resolved.TryGetValue(local, out var value):
                    instruction.SetOperand(i, value);
                    break;

                // A memory base/index must stay an address-holding local, so only a local replacement
                // is substituted there; a constant is left in place (which keeps the source Move alive).
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable baseLocal && resolved.TryGetValue(baseLocal, out var baseValue) && baseValue is LocalVariable baseReplacement)
                        memory.Base = baseReplacement;
                    if (memory.Index is LocalVariable indexLocal && resolved.TryGetValue(indexLocal, out var indexValue) && indexValue is LocalVariable indexReplacement)
                        memory.Index = indexReplacement;
                    instruction.SetOperand(i, memory); // MemoryOperand is a struct, write the copy back
                    break;

                // Same as a memory base: the object a field is read from must stay a local.
                case FieldReference { Local: { } fieldLocal } field when resolved.TryGetValue(fieldLocal, out var fieldValue) && fieldValue is LocalVariable fieldReplacement:
                    field.ReplaceLocal(fieldLocal, fieldReplacement);
                    break;
                case AddressOf { Target: FieldReference addressField } when addressField.RequiresReceiver
                    && resolved.TryGetValue(addressField.Local, out var receiverValue) && receiverValue is LocalVariable receiver:
                    addressField.ReplaceLocal(addressField.Local, receiver);
                    instruction.SetOperand(i, instruction.Operands[i]);
                    break;
            }
        }
    }

    // Every local read by some instruction. The single write position (a plain local destination) is
    // excluded; memory and field operands always contribute their address/object locals as reads.
    private static HashSet<LocalVariable> CollectReadLocals(ISILControlFlowGraph cfg)
    {
        var reads = new HashSet<LocalVariable>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
            {
                var destination = instruction.Destination;

                foreach (var operand in instruction.Operands)
                {
                    switch (operand)
                    {
                        case LocalVariable local when !ReferenceEquals(local, destination):
                            reads.Add(local);
                            break;
                        case MemoryOperand memory:
                            if (memory.Base is LocalVariable baseLocal)
                                reads.Add(baseLocal);
                            if (memory.Index is LocalVariable indexLocal)
                                reads.Add(indexLocal);
                            break;
                        case FieldReference field when field.Local is { } fieldLocal:
                            reads.Add(fieldLocal);
                            break;
                        case AddressOf { Target: LocalVariable addressed }:
                            reads.Add(addressed);
                            break;
                        case AddressOf { Target: FieldReference fieldAddress } when fieldAddress.RequiresReceiver:
                            reads.Add(fieldAddress.Local);
                            break;
                        case AddressOf { Target: ArrayAccess element }:
                            reads.Add(element.Array);
                            if (element.Index is LocalVariable elementIndex) reads.Add(elementIndex);
                            break;
                        case ArrayAccess access:
                            reads.Add(access.Array);
                            if (access.Index is LocalVariable index) reads.Add(index);
                            break;
                        case ArrayLength length:
                            reads.Add(length.Array);
                            break;
                    }
                }
            }

        return reads;
    }

    // Pure values that are safe to duplicate across uses: other locals (copies) and constants. Memory
    // field/array loads and lengths are snapshots/checks, not immutable constants.
    private static bool IsForwardable(IOperand value) =>
        value switch
        {
            LocalVariable => true,
            MemoryOperand => false,
            FieldReference => false,
            AddressOf { Target: FieldReference } => false,
            ArrayAccess or ArrayLength => false,
            // initobj defines mutable value-type storage. Its SSA local can
            // subsequently receive field writes (including HFA lane assembly)
            // without a second whole-local definition. Forwarding the initial
            // default into calls/returns would silently discard those writes.
            DefaultStructValue => false,
            _ => true
        };

    // Whole-local SSA does not version field writes. A managed aggregate copy
    // must remain a value copy, not turn two independently mutable slots into
    // aliases. Primitive and enum scalar propagation remains unchanged.
    internal static bool IsStructStorage(LocalVariable local) =>
        local.Type is { IsValueType: true, IsEnumType: false } type && type.Type is
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;

    internal static bool PreserveStructCopy(LocalVariable destination, IOperand source, HashSet<LocalVariable> mutable) =>
        source is LocalVariable local &&
        (IsStructStorage(destination) && mutable.Contains(destination) || IsStructStorage(local) && mutable.Contains(local));

    internal static HashSet<LocalVariable> MutableStructStorage(ISILControlFlowGraph graph)
    {
        var result = new HashSet<LocalVariable>();
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        var addresses = new HashSet<LocalVariable>();
        foreach (var instruction in graph.Instructions)
        {
            if (instruction.Destination is LocalVariable destination)
            {
                if (!definitions.TryGetValue(destination, out var sites)) definitions[destination] = sites = [];
                sites.Add(instruction);
            }
            foreach (var operand in instruction.Operands)
                if (operand is LocalVariable local && (local.IsReturnBuffer || local.IsThis && IsStructStorage(local)))
                    addresses.Add(local);
            // A field store changes its enclosing value without redefining the
            // whole local. An address escape may mutate that same storage.
            if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference field, _] })
                result.Add(field.Local);
            foreach (var operand in instruction.Operands)
                if (operand is AddressOf { Target: LocalVariable addressed }) result.Add(addressed);
                else if (operand is AddressOf { Target: FieldReference fieldAddress }
                    && fieldAddress.RequiresReceiver && IsStructStorage(fieldAddress.Local)) result.Add(fieldAddress.Local);
        }
        // The native ABI passes value-type this and hidden return buffers by
        // address, even though their pointee type annotates pointer registers.
        // Chase ONLY uniquely defined address copies; ordinary value parameters
        // and multiply-defined/unproved slots are not address evidence.
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var pair in definitions)
                if (pair.Value.Count == 1 && pair.Value[0] is { OpCode: OpCode.Move, Operands: [_, var source] }
                    && (source is AddressOf || source is LocalVariable local && addresses.Contains(local)))
                    changed |= addresses.Add(pair.Key);
        }
        result.ExceptWith(addresses);
        return result;
    }
}
