using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Remove null and bounds checks which are explicit in il2cpp but implicit in IL
public static class InjectedCheckRemover
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            if (block.BlockType != BlockType.TwoWay || block.Instructions.Count == 0)
                continue;

            var terminator = block.Instructions[^1];

            if (terminator.OpCode != OpCode.ConditionalJump)
                continue;

            if (terminator.Operands[0] is not Block target || block.Successors.Count != 2)
                continue;

            var fall = block.Successors.SingleOrDefault(s => !ReferenceEquals(s,target));
            if (fall == null) continue;
            var targetThrow = GetInjectedThrowType(target);
            var fallThrow = GetInjectedThrowType(fall);
            if ((targetThrow == null) == (fallThrow == null)) continue;
            var throwsWhenTrue = targetThrow != null;
            var thrownType = targetThrow ?? fallThrow!;
            var throwing = throwsWhenTrue ? target : fall;
            var surviving = throwsWhenTrue ? fall : target;

            if (terminator.Operands[1] is not LocalVariable condition
                || !defOf.TryGetValue(condition, out var definition)
                || !IsInjectedCheck(definition, thrownType, throwsWhenTrue))
                continue;

            // Removing a fallthrough throw must still branch to the surviving
            // target; simply nopping the branch would execute the throw.
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(surviving);

            block.Successors.Remove(throwing);
            throwing.Predecessors.Remove(block);
            block.CalculateBlockType();
            removedAny = true;
        }

        if (!removedAny)
            return;

        // delete any throw blocks
        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(cfg);
    }

    private static bool IsInjectedCheck(Instruction definition, string thrownType, bool throwsWhenTrue) =>
        thrownType switch
        {
            "System.NullReferenceException" => definition.Operands.Count == 3
                && (definition.Operands[1] is Immediate { Value: 0 } || definition.Operands[2] is Immediate { Value: 0 })
                && (throwsWhenTrue ? definition.OpCode == OpCode.CheckEqual : definition.OpCode == OpCode.CheckNotEqual),
            "System.IndexOutOfRangeException" => throwsWhenTrue && definition.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual,
            _ => false
        };

    // The full name of the exception if this block does nothing but throw an injected check's exception, else null.
    private static string? GetInjectedThrowType(Block block)
    {
        string? thrown = null;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Nop or OpCode.Interrupt:
                case OpCode.Return when thrown != null:
                    continue;

                case OpCode.Throw when thrown == null
                    && instruction.Operands is [TypeAnalysisContext { FullName: "System.NullReferenceException" or "System.IndexOutOfRangeException" } exception]:
                    thrown = exception.FullName;
                    continue;

                default:
                    return null;
            }
        }

        return thrown;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                defs[local] = instruction;

        return defs;
    }
}
