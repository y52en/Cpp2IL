using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Remove an automatic null helper only when the very next observable operation
// is a managed callvirt on that SAME value. The managed call retains the throw.
public static class ForwardNullCheckRecovery
{
    private const string HelperHash = "04831e6180d248d5984385074bf616e1db3587640830919a81190a5eb9ae0f69";
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, bool>> Proofs = new();

    internal static bool MatchesHelperBytes(byte[] bytes)
    {
        if (bytes.Length != 16) return false;
        using var sha = SHA256.Create();
        return string.Concat(sha.ComputeHash(bytes).Select(b => b.ToString("x2"))) == HelperHash;
    }

    internal static bool Prove(MethodAnalysisContext method, ulong address)
        => Proofs.GetValue(method.AppContext, _ => new()).GetOrAdd(address, candidate =>
        {
            try
            {
                var binary = method.AppContext.Binary;
                var offset = checked((int)binary.MapVirtualAddressToRaw(candidate));
                var content = binary.GetRawBinaryContent();
                return offset >= 0 && offset <= content.Length - 16 && MatchesHelperBytes(content.Slice(offset, 16).ToArray());
            }
            catch (Exception) { return false; }
        });

    internal static bool Uses(IOperand operand, LocalVariable value) => operand switch
    {
        LocalVariable local => ReferenceEquals(local, value),
        MemoryOperand memory => memory.Base != null && Uses(memory.Base, value) || memory.Index != null && Uses(memory.Index, value),
        AddressOf address => Uses(address.Target, value),
        FieldReference field => ReferenceEquals(field.Local, value) || field.Parent != null && Uses(field.Parent, value),
        ArrayAccess array => ReferenceEquals(array.Array, value) || Uses(array.Index, value),
        ArrayLength length => ReferenceEquals(length.Array, value),
        _ => false
    };

    internal static bool DefinitionDominates(ISILControlFlowGraph cfg, Instruction definition, Instruction use)
    {
        var definitions = cfg.Blocks.Where(b => b.Instructions.Contains(definition)).ToArray();
        var uses = cfg.Blocks.Where(b => b.Instructions.Contains(use)).ToArray();
        if (definitions.Length != 1 || uses.Length != 1) return false;
        return ReferenceEquals(definitions[0], uses[0])
            ? definitions[0].Instructions.IndexOf(definition) < definitions[0].Instructions.IndexOf(use)
            : new DominatorInfo(cfg).Dominates(definitions[0], uses[0]);
    }

    internal static bool FollowedBySameVirtualReceiver(ISILControlFlowGraph cfg, Instruction guard)
    {
        if (guard is not { OpCode: OpCode.Call, Operands: [Immediate, LocalVariable result, LocalVariable input, ..] }
            || input.Type?.IsValueType == true
            || cfg.Instructions.Any(i => !ReferenceEquals(i, guard) && i.Operands.Any(o => Uses(o, result)))) return false;
        var homes = cfg.Blocks.Where(b => b.Instructions.Contains(guard)).ToArray();
        if (homes.Length != 1) return false;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        LocalVariable Root(LocalVariable value)
        {
            var seen = new HashSet<LocalVariable>();
            while (seen.Add(value) && definitions.TryGetValue(value, out var definition)
                   && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }) value = source;
            return value;
        }
        var root = Root(input);
        // A successful managed allocation cannot yield null. Keep its possible
        // allocation exception, and remove only a subsequent redundant check.
        if (definitions.TryGetValue(root, out var allocation)
            && allocation is { OpCode: OpCode.NewArr, Operands: [_, SzArrayTypeAnalysisContext, _] }
            && DefinitionDominates(cfg, allocation, guard)) return true;
        var current = homes[0]; var start = current.Instructions.IndexOf(guard) + 1;
        var visited = new HashSet<Block>(); var budget = 128;
        while (visited.Count < 8 && visited.Add(current))
        {
            foreach (var instruction in current.Instructions.Skip(start))
            {
                if (--budget < 0) return false;
                if (instruction.OpCode == OpCode.Nop) continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, LocalVariable or Immediate or TypeAnalysisContext] })
                {
                    if (ReferenceEquals(destination, root) || ReferenceEquals(destination, input)) return false;
                    continue;
                }
                if (instruction.OpCode == OpCode.Jump && ReferenceEquals(instruction, current.Instructions.LastOrDefault())) continue;
                if (instruction.OpCode is not (OpCode.Call or OpCode.CallVoid) || !instruction.NativeVirtualDispatch
                    || instruction.Operands[0] is not MethodAnalysisContext { IsStatic: false }) return false;
                var receiverIndex = instruction.OpCode == OpCode.Call ? 2 : 1;
                return instruction.Operands.Count > receiverIndex && instruction.Operands[receiverIndex] is LocalVariable receiver
                    && receiver.Type?.IsValueType != true && ReferenceEquals(Root(receiver), root);
            }
            if (current.Successors.Count != 1) return false;
            var next = current.Successors[0];
            // Never cross another path's join or exception/exit block.
            if (next == cfg.ExitBlock || next.Predecessors.Count != 1 || next.Predecessors[0] != current) return false;
            current = next; start = 0;
        }
        return false;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4) return 0;
        var changed = 0; var cfg = method.ControlFlowGraph!;
        foreach (var block in cfg.Blocks)
        foreach (var instruction in block.Instructions)
            if (instruction is { OpCode: OpCode.Call, Operands: [Immediate helper, ..] }
                && Prove(method, helper.UnsignedValue) && FollowedBySameVirtualReceiver(cfg, instruction))
            {
                instruction.OpCode = OpCode.Nop; instruction.SetOperands(); block.CalculateBlockType(); changed++;
            }
        return changed;
    }
}
