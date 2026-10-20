using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Reassemble complete, byte-covered stack copies from a proven large return.
// A single vector load is NOT an assignment of the entire returned struct.
public static class WholeStackValueCopyRecovery
{
    private sealed record Chunk(Register Temporary, int Source, int Width, Instruction Load);

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet) return 0;
        var graph = method.ControlFlowGraph!;
        if (graph.Instructions.Any(i => i.OpCode == OpCode.IndirectJump)) return 0;
        if(method.AppContext.InstructionSet.CallingConventionResolver is not Arm64CallingConventionResolver resolver)return 0;
        var changed = 0;
        foreach (var block in graph.Blocks.ToArray())
        foreach (var call in block.Instructions.ToArray())
        {
            if (call is not { OpCode: OpCode.Call, Operands: [Immediate address, Register storage, ..] }
                || !Offset(storage, out _) || !method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue, out var targets)
                || targets.Count == 0) continue;
            var size = resolver.ReturnStorageSize(targets[0]);
            if (size is <= 16 or > 4096 || targets.Any(t => !resolver.ReturnsViaHiddenBuffer(t)
                    || resolver.HiddenReturnBufferRegister(t)?.Name != "X8"
                    || resolver.ReturnStorageSize(t) != size)) continue;
            if (Recover(graph, block, block.Instructions.IndexOf(call) + 1, storage, (int)size)) changed++;
        }
        return changed;
    }

    public static bool Recover(ISILControlFlowGraph graph, Block firstBlock, int start, Register storage, int size)
    {
        if (size is <= 0 or > 4096 || !Offset(storage, out var basis)) return false;
        var chunks = new Dictionary<string, Chunk>();
        var loads = new HashSet<Instruction>();
        var stores = new List<Instruction>();
        var covered = new HashSet<int>();
        var visited = new HashSet<Block>();
        int? destination = null;
        var block = firstBlock;
        var scanned = 0;
        while (visited.Add(block))
        {
            for (var index = start; index < block.Instructions.Count && ++scanned <= 96; index++)
            {
                var instruction = block.Instructions[index];
                if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
                if (instruction.OpCode != OpCode.Move || instruction.Operands.Count != 2) return false;
                var isStore = instruction.Operands[0] is Register writtenSlot && Offset(writtenSlot, out _);
                if (isStore)
                {
                    if (instruction.Operands[1] is not Register temporary || !chunks.TryGetValue(temporary.Name, out var chunk)
                        || instruction.NativeWriteSize != chunk.Width) return false;
                    Offset((Register)instruction.Operands[0], out var target);
                    var relative = chunk.Source - basis;
                    var proposed = (long)target - relative;
                    if (proposed is < int.MinValue or > int.MaxValue) return false;
                    destination ??= (int)proposed;
                    if (destination != proposed || (long)destination < (long)basis + size
                        && (long)basis < (long)destination + size) return false;
                    for (var b = relative; b < relative + chunk.Width; b++)
                        if (!covered.Add(b)) return false;
                    stores.Add(instruction); loads.Add(chunk.Load);
                    if (covered.Count != size) continue;
                    // Stores must be one uninterrupted copy: no intervening read
                    // can observe a partially changed destination during collapse.
                    var firstStore = block.Instructions.IndexOf(stores[0]);
                    if (firstStore < 0 || block.Instructions.Skip(firstStore).Take(index - firstStore + 1)
                        .Any(i => i.OpCode != OpCode.Nop && !stores.Contains(i))) return false;
                    var destinationRegister = (Register)stores[0].Operands[0];
                    // The first physical store may be the last chunk (ARM64
                    // commonly stores +32 before +0). Use the proven base.
                    destinationRegister = new Register(null, SlotName(destination.Value));
                    stores[0].SetOperands(destinationRegister, storage);
                    stores[0].NativeReadSize = stores[0].NativeWriteSize = 0;
                    // Keep the physical loads: their register values may also
                    // feed another consumer. Only the proven destination stores
                    // are represented by this logical assignment. Ordinary DCE
                    // may later remove loads once their users truly disappear.
                    foreach (var obsolete in stores.Skip(1))
                    { obsolete.OpCode = OpCode.Nop; obsolete.SetOperands(); obsolete.NativeReadSize = obsolete.NativeWriteSize = 0; }
                    return true;
                }
                if (instruction.Destination is not Register destinationRegisterRead) return false;
                // A chunk value cannot have any consumer other than its exact
                // matched store, and unknown writes cannot alias the source.
                if (chunks.Keys.Any(name => Reads(instruction, name))) return false;
                chunks.Remove(destinationRegisterRead.Name);
                if (instruction.Operands[1] is Register source && Offset(source, out var offset)
                    && instruction.NativeReadSize is 1 or 2 or 4 or 8 or 16)
                {
                    var delta = (long)offset - basis;
                    if (delta < 0 || delta + instruction.NativeReadSize > size) return false;
                    chunks[destinationRegisterRead.Name] = new(destinationRegisterRead, offset,
                        instruction.NativeReadSize, instruction);
                }
                else if (stores.Count != 0) return false;
            }
            if (scanned > 96 || stores.Count != 0 || block.Successors.Count != 1
                || block.Successors[0].Predecessors.Count != 1) return false;
            block = block.Successors[0]; start = 0;
        }
        return false;
    }

    private static bool Reads(Instruction instruction, string name) => instruction.Sources.Any(operand => operand switch
    {
        Register r => r.Name == name,
        AddressOf { Target: Register r } => r.Name == name,
        MemoryOperand m => m.Base is Register b && b.Name == name || m.Index is Register i && i.Name == name,
        _ => false
    }) || instruction.OpCode == OpCode.Throw && instruction.Operands.Any(o => o is Register r && r.Name == name);

    private static bool Offset(Register register, out int offset)
    {
        offset = 0;
        if (!register.Name.StartsWith("stack_", StringComparison.Ordinal)) return false;
        var value = register.Name.Substring(6); var negative = value.StartsWith("-", StringComparison.Ordinal);
        if (negative) value = value.Substring(1);
        if (!int.TryParse(value, NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture, out var magnitude) || magnitude < 0) return false;
        offset = negative ? -magnitude : magnitude; return true;
    }

    private static string SlotName(int offset) => offset < 0 ? "stack_-" + (-offset).ToString("X") : "stack_" + offset.ToString("X");
}
