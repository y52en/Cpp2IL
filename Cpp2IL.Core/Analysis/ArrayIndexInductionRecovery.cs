using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class ArrayIndexInductionRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = new Dictionary<LocalVariable, Instruction?>();
        foreach (var instruction in instructions)
            if (instruction.Destination is LocalVariable local)
                definitions[local] = definitions.ContainsKey(local) ? null : instruction;
        var changed = false;
        foreach (var access in instructions.SelectMany(i => i.Operands).OfType<ArrayAccess>())
        {
            if (access.Array.Type is not SzArrayTypeAnalysisContext
                || access.Index is not LocalVariable { Type: null } index) continue;
            var visiting = new HashSet<LocalVariable>();
            var proved = new HashSet<LocalVariable>();
            var sawSeed = false; var sawPhi = false; var sawUpdate = false;
            bool Prove(IOperand operand, int depth)
            {
                if (depth > 64) return false;
                if (operand is Immediate immediate)
                {
                    // A small nonnegative seed has the same value even when
                    // MOV Wn zero-extends it; don't guess negative seed widths.
                    sawSeed |= immediate.Value is >= 0 and <= int.MaxValue;
                    return immediate.Value is >= 0 and <= int.MaxValue;
                }
                if (operand is not LocalVariable local) return false;
                if (local.Type != null) return false; // Metadata wins; no casts or pointer guesses.
                if (proved.Contains(local) || visiting.Contains(local)) return true;
                if (!definitions.TryGetValue(local, out var definition) || definition == null) return false;
                visiting.Add(local);
                var valid = false;
                if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                    valid = Prove(source, depth + 1);
                else if (definition.OpCode == OpCode.Phi && definition.Operands.Count >= 3)
                {
                    sawPhi = true;
                    valid = definition.Operands.Skip(1).All(source => Prove(source, depth + 1));
                }
                else if (definition.OpCode is OpCode.Add or OpCode.Subtract
                    && definition.NativeArithmeticSize == 8
                    && definition.Operands is [_, LocalVariable previous, Immediate step]
                    && step.Value is >= int.MinValue and <= int.MaxValue)
                {
                    sawUpdate = true;
                    valid = Prove(previous, depth + 1);
                }
                visiting.Remove(local);
                if (valid) proved.Add(local);
                return valid;
            }
            if (!Prove(index, 0) || !sawSeed || !sawPhi || !sawUpdate) continue;
            // All ancestors are constants/copies/phis/native-64-bit updates,
            // and this value is a proven managed array index, not its address.
            foreach (var local in proved)
                if (local.Type == null) { local.Type = method.AppContext.SystemTypes.SystemInt64Type; changed = true; }
        }
        return changed;
    }
}
