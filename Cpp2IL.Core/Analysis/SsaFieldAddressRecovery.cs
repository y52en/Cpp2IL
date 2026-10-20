using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Normalize an exact pointer-width ADD with single-definition pointer AND root.
// The same local proofs are required after coalescing; arbitrary merged values
// are not accepted merely because they have a plausible type annotation.
// Does not move the memory operation, infer a pointer type, or guess a field.
// The existing metadata resolver owns the resulting [object+offset] access.
public static class SsaFieldAddressRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg || method.AppContext.Binary.PointerSizeBytes != 8) return 0;
        if (!cfg.Instructions.Any(i => i.OpCode == OpCode.Add && i.NativeArithmeticSize == 8)) return 0;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var dominance = new DominatorInfo(cfg); var changed = 0;
        var trace = System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_FIELD_ADDRESS_RVA") == method.UnderlyingPointer.ToString("X");
        foreach (var block in cfg.Blocks)
        foreach (var instruction in block.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count != 2) continue;
            for (var n = 0; n < 2; n++)
            {
                var width = n == 0 ? instruction.NativeWriteSize : instruction.NativeReadSize;
                if (trace && instruction.Operands[n] is MemoryOperand { Base: LocalVariable probePointer }
                    && definitions.TryGetValue(probePointer, out var probeAddress) && probeAddress.OpCode == OpCode.Add)
                    System.Console.Error.WriteLine("FIELD_ADDRESS index=" + instruction.Index + " width=" + width
                        + " address=" + probeAddress + " native_width=" + probeAddress.NativeArithmeticSize
                        + " source_type=" + (probeAddress.Operands[1] as LocalVariable)?.Type?.Type
                        + " source_writes=" + cfg.Instructions.Count(i => ReferenceEquals(i.Destination, probeAddress.Operands[1])));
                if (width <= 0 || instruction.Operands[n] is not MemoryOperand
                    { Base: LocalVariable pointer, Index: null, Scale: 0, Addend: >= 0 } memory
                    || !definitions.TryGetValue(pointer, out var address)
                    || address is not { OpCode: OpCode.Add, NativeArithmeticSize: 8,
                        Operands: [_, LocalVariable { Type: { IsValueType: false } type } root, Immediate { Value: >= 0 } offset] }
                    || type.Type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST or Il2CppTypeEnum.IL2CPP_TYPE_STRING)
                    || offset.Value > int.MaxValue - memory.Addend) continue;
                if (cfg.Instructions.Any(i => i.ImplicitDefinition != null
                    && (Equals(i.ImplicitDefinition, pointer.Register) || Equals(i.ImplicitDefinition, root.Register)))) continue;
                var addressOwner = cfg.Blocks.Single(b => b.Instructions.Contains(address));
                bool Before(Instruction definition, Block home, Instruction consumer, Block use)
                    => ReferenceEquals(home, use) ? home.Instructions.IndexOf(definition) < home.Instructions.IndexOf(consumer)
                        : dominance.Dominates(home, use);
                if (!Before(address, addressOwner, instruction, block)) continue;
                var rootWrites = cfg.Instructions.Where(i => ReferenceEquals(i.Destination, root)).ToArray();
                if (!(method.ParameterLocals.Contains(root) && rootWrites.Length == 0))
                {
                    if (rootWrites.Length != 1) continue;
                    var rootOwner = cfg.Blocks.Single(b => b.Instructions.Contains(rootWrites[0]));
                    if (!Before(rootWrites[0], rootOwner, address, addressOwner)) continue;
                }
                instruction.SetOperand(n, new MemoryOperand(root, addend: offset.Value + memory.Addend)); changed++;
            }
        }
        return changed;
    }
}
