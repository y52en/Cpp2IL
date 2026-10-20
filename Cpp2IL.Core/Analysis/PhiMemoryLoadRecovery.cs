using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Distribute ONE leading read over a pointer phi, before SSA destruction.
// No speculative read: every predecessor has only this successor. No read
// crosses a call/store/other instruction in the join. This preserves each
// edge's pointer provenance instead of merging static storage and array data.
public static class PhiMemoryLoadRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg) return 0;
        var count = 0;
        foreach (var block in cfg.Blocks.ToArray())
        {
            var load = block.Instructions.FirstOrDefault(i => i.OpCode is not (OpCode.Phi or OpCode.Nop));
            if (load is not { OpCode: OpCode.Move, NativeReadSize: > 0,
                Operands: [LocalVariable value, MemoryOperand { Base: LocalVariable pointer, Index: null, Scale: 0 } memory] }
                || ReferenceEquals(value, pointer) || block.Predecessors.Count < 2
                || block.Predecessors.Distinct().Count() != block.Predecessors.Count) continue;
            var definitions = cfg.Instructions.Where(i => ReferenceEquals(i.Destination, pointer)).ToArray();
            if (definitions is not [Instruction { OpCode: OpCode.Phi } phi]
                || !block.Instructions.Contains(phi) || phi.Operands.Count != block.Predecessors.Count + 1
                || phi.Operands.Skip(1).Any(o => o is not LocalVariable || ReferenceEquals(o, pointer))
                || cfg.Instructions.Count(i => ReferenceEquals(i.Destination, value)) != 1
                || block.Predecessors.Any(p => p.Successors.Count != 1 || !ReferenceEquals(p.Successors[0], block)
                    || ReferenceEquals(p, cfg.EntryBlock) || ReferenceEquals(p, cfg.ExitBlock)
                    || ReferenceEquals(p, block)
                    || p.Instructions.LastOrDefault()?.OpCode is OpCode.ConditionalJump or OpCode.IndirectJump or OpCode.Return or OpCode.Throw)
                || cfg.Instructions.Where(i => !ReferenceEquals(i, phi) && !ReferenceEquals(i, load))
                    .Any(i => i.Operands.Any(o => Contains(o, pointer)))) continue;
            var dominance = new DominatorInfo(cfg);
            var valid = true;
            for (var n = 0; n < block.Predecessors.Count; n++)
            {
                var input = (LocalVariable)phi.Operands[n + 1]; var predecessor = block.Predecessors[n];
                var writes = cfg.Instructions.Where(i => ReferenceEquals(i.Destination, input)).ToArray();
                if (method.ParameterLocals.Contains(input) && writes.Length == 0) continue;
                if (writes.Length != 1) { valid = false; break; }
                var owner = cfg.Blocks.SingleOrDefault(b => b.Instructions.Contains(writes[0]));
                if (owner == null || !dominance.Dominates(owner, predecessor)) { valid = false; break; }
            }
            if (!valid) continue;
            var inputs = new IOperand[phi.Operands.Count]; inputs[0] = value;
            for (var n = 0; n < block.Predecessors.Count; n++)
            {
                var predecessor = block.Predecessors[n];
                var edgeValue = new LocalVariable("phi_read_" + block.ID + "_" + n,
                    new(null, "phi_read_" + block.ID + "_" + n), value.Type);
                method.Locals.Add(edgeValue); inputs[n + 1] = edgeValue;
                IOperand edgeSource = new MemoryOperand(phi.Operands[n + 1], addend: memory.Addend);
                // Preserve a known object's split field address as [object+offset],
                // not an untyped pointer that survives until IL emission. This
                // is one exact SSA ADD, not recursive affine guessing. The usual
                // metadata/width resolver still owns the field identification.
                var incoming = (LocalVariable)phi.Operands[n + 1];
                var addressWrites = cfg.Instructions.Where(i => ReferenceEquals(i.Destination, incoming)).ToArray();
                if (addressWrites is [Instruction { OpCode: OpCode.Add,
                    Operands: [_, LocalVariable { Type: { IsValueType: false } ownerType } root, Immediate offset] }]
                    && ownerType is not (RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext
                        or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
                    && offset.Value >= 0 && memory.Addend >= 0 && offset.Value <= int.MaxValue - memory.Addend
                    && cfg.Instructions.Count(i => ReferenceEquals(i.Destination, root)) <= 1)
                    edgeSource = new MemoryOperand(root, addend: offset.Value + memory.Addend);
                var edgeLoad = new Instruction(load.Index, OpCode.Move, edgeValue, edgeSource) { NativeReadSize = load.NativeReadSize };
                var insertion = predecessor.Instructions.Count;
                if (predecessor.Instructions.LastOrDefault()?.OpCode == OpCode.Jump) insertion--;
                predecessor.Instructions.Insert(insertion, edgeLoad);
            }
            phi.SetOperands(inputs.ToList()); block.Instructions.Remove(load); count++;
        }
        return count;
    }

    private static bool Contains(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable v => ReferenceEquals(v, local),
        MemoryOperand m => m.Base != null && Contains(m.Base, local) || m.Index != null && Contains(m.Index, local),
        FieldReference f => ReferenceEquals(f.Local, local) || f.Parent != null && Contains(f.Parent, local),
        ArrayAccess a => ReferenceEquals(a.Array, local) || Contains(a.Index, local),
        ArrayLength a => ReferenceEquals(a.Array, local), AddressOf a => Contains(a.Target, local), _ => false
    };
}
