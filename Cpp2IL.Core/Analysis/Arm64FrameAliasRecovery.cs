using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

/// <summary>Proven native frame addresses only. Not managed type or EH recovery.</summary>
public static class Arm64FrameAliasRecovery
{
    private static bool Gpr(string name) => name.StartsWith("X", StringComparison.Ordinal)
        && int.TryParse(name.Substring(1), out var number) && number is >= 0 and <= 30;

    private static bool Equal(Dictionary<string, int> a, Dictionary<string, int> b) =>
        a.Count == b.Count && a.All(p => b.TryGetValue(p.Key, out var value) && value == p.Value);

    private static Dictionary<string, int>? Incoming(Block block, ISILControlFlowGraph graph,
        Dictionary<Block, Dictionary<string, int>?> outputs)
    {
        if (block == graph.EntryBlock) return [];
        // Unvisited is TOP, not the proven absence of an alias. Starting every
        // backedge at empty destroys even a frame preserved by the whole loop.
        // Only a path anchored at the real entry can initialize a state.
        var known=block.Predecessors.Select(p=>outputs[p]).Where(s=>s!=null).ToArray();
        if(known.Length==0)return null;
        var result = new Dictionary<string, int>(known[0]!);
        foreach (var predecessor in known.Skip(1))
            foreach (var key in result.Keys.ToArray())
                if (!predecessor!.TryGetValue(key, out var value) || value != result[key])
                    result.Remove(key);
        return result;
    }

    private static int? Address(Instruction instruction, int size, Dictionary<string, int> aliases)
    {
        long? value = null;
        if (instruction is { OpCode: OpCode.Move, NativeRegisterCopySize: 8 })
        {
            if (instruction.Operands[1] is AddressOf { Target: StackOffset slot })
                value = (long)size + slot.Offset;
            else if (instruction.Operands[1] is Register source && aliases.TryGetValue(source.Name, out var copied))
                value = copied;
        }
        else if (instruction.OpCode is OpCode.Add or OpCode.Subtract && instruction.NativeArithmeticSize == 8
            && instruction.Operands[1] is Register baseRegister
            && aliases.TryGetValue(baseRegister.Name, out var address)
            && instruction.Operands[2] is Immediate immediate)
        {
            // Bound the immediate before arithmetic; long.MinValue must not wrap.
            if (immediate.Value is >= int.MinValue and <= int.MaxValue)
                value = (long)address + (instruction.OpCode == OpCode.Add ? immediate.Value : -immediate.Value);
        }
        return value is >= int.MinValue and <= int.MaxValue ? (int)value.Value : null;
    }

    private static void Transfer(Instruction instruction, int size, Dictionary<string, int> aliases)
    {
        var address = Address(instruction, size, aliases);
        if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall or OpCode.Newobj
            or OpCode.Box or OpCode.Unbox)
            foreach (var key in aliases.Keys.ToArray())
                if (Gpr(key) && (int.Parse(key.Substring(1)) <= 18 || key == "X30")) aliases.Remove(key);
        if (instruction.ImplicitDefinition is { } implicitRegister) aliases.Remove(implicitRegister.Name);
        if (instruction.Destination is not Register destination) return;
        aliases.Remove(destination.Name);
        if (Gpr(destination.Name) && address is { } offset) aliases[destination.Name] = offset;
    }

    public static int Recover(ISILControlFlowGraph graph, IReadOnlyDictionary<Instruction, int> stackSizes)
    {
        // No inferred successors for computed jumps: do not treat missing edges as proof.
        if (graph.Instructions.Any(i => i.OpCode == OpCode.IndirectJump)) return 0;
        var outputs = graph.Blocks.ToDictionary(b => b, _ => (Dictionary<string, int>?)null);
        var stable = false;
        for (var round = 0; round < 4096; round++)
        {
            var changed = false;
            foreach (var block in graph.Blocks)
            {
                var state = Incoming(block, graph, outputs);
                if(state==null)continue;
                foreach (var instruction in block.Instructions)
                {
                    if (!stackSizes.TryGetValue(instruction, out var size)) return 0;
                    Transfer(instruction, size, state);
                }
                if (outputs[block] is {} previous && Equal(state, previous)) continue;
                outputs[block] = state;
                changed = true;
            }
            if (!changed) { stable = true; break; }
        }
        if (!stable) return 0;

        // Compute every rewrite against the settled, unmodified graph first.
        var rewrites = new List<(Instruction Instruction, int Operand, IOperand Value)>();
        foreach (var block in graph.Blocks)
        {
            var state = Incoming(block, graph, outputs);
            if(state==null)continue; // unreachable/unanchored cycles prove nothing
            foreach (var instruction in block.Instructions)
            {
                var size = stackSizes[instruction];
                var address = Address(instruction, size, state);
                for (var operand = 0; operand < instruction.Operands.Count; operand++)
                {
                    if (instruction.Operands[operand] is not MemoryOperand
                        { Index: null, Scale: 0, Base: Register baseRegister } memory
                        || !state.TryGetValue(baseRegister.Name, out var frame)
                        || memory.Addend is < int.MinValue or > int.MaxValue) continue;
                    var relative = (long)frame + memory.Addend - size;
                    if (relative is >= int.MinValue and <= int.MaxValue)
                        rewrites.Add((instruction, operand, new StackOffset((int)relative)));
                }
                if (address is { } absolute && instruction.OpCode is OpCode.Add or OpCode.Subtract)
                {
                    var relative = (long)absolute - size;
                    if (relative is >= int.MinValue and <= int.MaxValue)
                        rewrites.Add((instruction, -1, new AddressOf(new StackOffset((int)relative))));
                }
                Transfer(instruction, size, state);
            }
        }
        foreach (var (instruction, operand, value) in rewrites)
            if (operand >= 0) instruction.SetOperand(operand, value);
            else
            {
                var destination = instruction.Operands[0];
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(destination, value);
                instruction.NativeRegisterCopySize = 8;
            }
        return rewrites.Count;
    }
}
