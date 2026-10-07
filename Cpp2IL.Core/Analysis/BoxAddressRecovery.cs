using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A native address names storage, not its value at address-computation time.
/// Delay a pure stack address until its first, positively identified boxing read
/// when a store intervenes. SSA must see the stored value, not the live-in slot.
/// This does not rewrite unknown calls or move anything across a CFG edge/call.
/// </summary>
public static class BoxAddressRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var keys = method.AppContext.GetOrCreateKeyFunctionAddresses();
        var targets = new HashSet<ulong> { keys.il2cpp_value_box, keys.il2cpp_vm_object_box };
        targets.Remove(0);
        Run(method.ControlFlowGraph!, targets);
    }

    public static int Run(ISILControlFlowGraph graph, ISet<ulong> boxTargets)
    {
        var changes = 0;
        foreach (var block in graph.Blocks)
        {
            var instructions = block.Instructions;
            foreach (var address in instructions.ToArray())
            {
                if (address is not { OpCode: OpCode.Move, Operands: [Register pointer, AddressOf { Target: Register slot }] }
                    || !slot.Name.StartsWith("stack_")) continue;
                var start = instructions.IndexOf(address);
                var stored = false;
                for (var i = start + 1; i < instructions.Count; i++)
                {
                    var instruction = instructions[i];
                    if (instruction.Sources.Contains(pointer))
                    {
                        if (stored && instruction.OpCode == OpCode.Call
                            && instruction.Operands.Count >= 4
                            && instruction.Operands[0] is Immediate target && boxTargets.Contains(target.UnsignedValue)
                            && instruction.Operands[3] is Register valuePointer && valuePointer == pointer)
                        {
                            instructions.RemoveAt(start);
                            instructions.Insert(i - 1, address);
                            changes++;
                        }
                        break;
                    }
                    if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall
                        || instruction.Destination is Register written && written == pointer
                        || instruction.ImplicitDefinition is { } clobbered && clobbered == pointer) break;
                    if (instruction.Destination is Register destination && destination == slot) stored = true;
                }
            }
        }
        return changes;
    }
}
