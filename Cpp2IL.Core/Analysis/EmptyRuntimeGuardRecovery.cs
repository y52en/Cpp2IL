using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Known init calls can disappear before argument trimming makes the remaining
// init region empty. This pass removes no call or application operation: it
// only collapses the now-empty, reconverging native class-flag branch.
public static class EmptyRuntimeGuardRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018
            || method.AppContext.UnityVersion.Minor != 4) return 0;
        var requested = System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_EMPTY_GUARD_RVAS");
        var trace = requested != null && requested.Split(',').Any(r => string.Equals(r.Trim(),
            method.UnderlyingPointer.ToString("X"), System.StringComparison.OrdinalIgnoreCase));
        return RecoverToFixedPoint(method.ControlFlowGraph!, trace ? System.Console.WriteLine : null);
    }

    public static int RecoverToFixedPoint(ISILControlFlowGraph cfg, System.Action<string>? trace = null)
    {
        var count=0;
        var changed=true;
        while(changed)
        {
            changed=false;
            foreach(var guard in cfg.Blocks.ToArray())
            {
                if(!cfg.Blocks.Contains(guard))continue;
                trace?.Invoke("EMPTY_GUARD_BEFORE " + guard);
                var recovered=TryRecover(cfg,guard);
                trace?.Invoke("EMPTY_GUARD_RESULT " + guard.ID + " " + recovered);
                if(recovered){count++;changed=true;}
            }
            // Collapsing a later flag test can make earlier branch-local class
            // pointer copies dead. Reconsider only after proven dead code is
            // removed; every successful rewrite removes at least one block.
            if(changed)DeadCodeEliminator.Run(cfg);
        }
        return count;
    }

    public static bool TryRecover(ISILControlFlowGraph cfg, Block guard)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.LastOrDefault() is not
                { OpCode: OpCode.ConditionalJump, Operands: [Block destination, LocalVariable predicate] }
            || !guard.Successors.Contains(destination)) return false;
        var tests = guard.Instructions.Where(i => ReferenceEquals(i.Destination, predicate)).ToArray();
        if (tests.Length != 1 || tests[0] is not
            { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, LocalVariable masked, Immediate { Value: 0 }] }) return false;
        var masks = guard.Instructions.Where(i => ReferenceEquals(i.Destination, masked)).ToArray();
        if (masks.Length != 1 || masks[0] is not
            { OpCode: OpCode.And, Operands: [_, var flagValue, Immediate mask] }
            || RuntimeClassFlagSnapshot.Resolve(cfg,guard,masks[0],flagValue) is not
                MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext }, Index: null, Scale: 0 } flag
            || !((flag.Addend == 0x126 && mask.Value == 1) || (flag.Addend == 0x127 && mask.Value == 2))) return false;
        return Collapse(cfg, guard, guard.Successors[0], guard.Successors[1])
            || Collapse(cfg, guard, guard.Successors[1], guard.Successors[0]);
    }

    private static bool Collapse(ISILControlFlowGraph cfg, Block guard, Block entry, Block merge)
    {
        if (merge == cfg.EntryBlock || merge == cfg.ExitBlock
            || merge.Instructions.Any(i => i.OpCode == OpCode.Phi)) return false;
        var region = new HashSet<Block>();
        var previous = guard;
        var current = entry;
        while (current != merge)
        {
            if (region.Count >= 8 || !region.Add(current) || current == guard
                || current == cfg.EntryBlock || current == cfg.ExitBlock
                || current.Predecessors.Count != 1 || current.Predecessors[0] != previous
                || current.Successors.Count != 1
                || current.Instructions.Any(i => i.OpCode is not (OpCode.Nop or OpCode.Jump))
                || current.Instructions.LastOrDefault() is not
                    { OpCode: OpCode.Jump, Operands: [Block next] }
                || next != current.Successors[0]) return false;
            previous = current;
            current = next;
        }
        if (region.Count == 0) return false;
        MetadataInitGuardRemover.Excise(cfg, guard, entry, merge, region);
        return true;
    }
}
