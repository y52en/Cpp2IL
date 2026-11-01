using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Late metadata/stack recovery runs after the SSA type fixpoint. Recover only
// exact scalar facts for single-definition, nonescaping logical values. Native
// register width alone never proves that an address is a managed integer.
public static class LateScalarTypeRecovery
{
    private static bool Integral(TypeAnalysisContext? type) => type?.FullName is
        "System.SByte" or "System.Byte" or "System.Int16" or "System.UInt16" or "System.Char"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64";

    private static bool Contains(IOperand? operand, LocalVariable value) => operand switch
    {
        LocalVariable local => ReferenceEquals(local, value),
        AddressOf address => Contains(address.Target, value),
        MemoryOperand memory => Contains(memory.Base, value) || Contains(memory.Index, value),
        FieldReference field => ReferenceEquals(field.Local, value) || Contains(field.Parent, value),
        ArrayAccess array => ReferenceEquals(array.Array, value) || Contains(array.Index, value),
        ArrayLength length => ReferenceEquals(length.Array, value),
        _ => false
    };

    private static bool EscapesAsAddress(IOperand operand, LocalVariable value) => operand switch
    {
        AddressOf address => Contains(address.Target, value),
        MemoryOperand memory => Contains(memory.Base, value)
            || memory.Index != null && EscapesAsAddress(memory.Index, value),
        FieldReference field => ReferenceEquals(field.Local, value)
            || field.Parent != null && EscapesAsAddress(field.Parent, value),
        ArrayAccess array => ReferenceEquals(array.Array, value) || EscapesAsAddress(array.Index, value),
        ArrayLength length => ReferenceEquals(length.Array, value),
        _ => false
    };

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not {} graph) return 0;
        var instructions = graph.Instructions.ToArray();
        if (!instructions.Any(i => i.Destination is LocalVariable {Type: null}
            && i.Operands.Any(o => o is LocalVariable local && Integral(local.Type)
                || o is FieldReference field && Integral(field.Field.FieldType)))) return 0;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var homes = graph.Blocks.SelectMany(b => b.Instructions.Select((i, n) => (i, b, n)))
            .GroupBy(x => x.i).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var dominance = new DominatorInfo(graph);
        var implicitWrites = instructions.Where(i => i.ImplicitDefinition != null)
            .Select(i => (i.ImplicitDefinition!.Value.Number, i.ImplicitDefinition.Value.Name)).ToHashSet();
        var safeResults = new Dictionary<LocalVariable, bool>();

        bool Dominates(Instruction definition, Instruction use)
            => homes.TryGetValue(definition, out var a) && homes.TryGetValue(use, out var b)
                && (ReferenceEquals(a.b, b.b) ? a.n < b.n : dominance.Dominates(a.b, b.b));
        bool Clobbered(LocalVariable local) => implicitWrites.Contains((local.Register.Number, local.Register.Name));
        bool StableAt(LocalVariable local, Instruction use)
        {
            if (Clobbered(local)) return false;
            if (!definitions.TryGetValue(local, out var values)) return method.ParameterLocals.Contains(local);
            return values.Length == 1 && Dominates(values[0], use);
        }
        bool SafeResult(LocalVariable local, Instruction definition)
        {
            if (method.ParameterLocals.Contains(local) || Clobbered(local)
                || !definitions.TryGetValue(local, out var values) || values.Length != 1) return false;
            var used = false;
            foreach (var instruction in instructions)
                for (var index = 0; index < instruction.Operands.Count; index++)
                {
                    var operand = instruction.Operands[index];
                    // Exclude only the actual write slot, not a repeated input.
                    var write = instruction.OpCode is OpCode.Call or OpCode.IndirectCall ? 1 : 0;
                    if (index == write && ReferenceEquals(operand, instruction.Destination)) continue;
                    if (!Contains(operand, local)) continue;
                    used = true;
                    if (EscapesAsAddress(operand, local) || !Dominates(definition, instruction)) return false;
                }
            return used;
        }

        var changes = 0;
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var instruction in instructions)
            {
                if (instruction.Destination is not LocalVariable {Type: null} result) continue;
                TypeAnalysisContext? type = null;
                if (instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
                    && instruction.NativeArithmeticSize is 4 or 8 && instruction.NativeFloatingPointSize == 0
                    && instruction.Operands is [_, var left, var right])
                {
                    bool Known(IOperand operand) => operand is LocalVariable local
                        && Integral(local.Type) && StableAt(local, instruction);
                    if ((Known(left) || Known(right))
                        && (Known(left) || left is Immediate) && (Known(right) || right is Immediate))
                        // W writes clear the upper half of X. Retain unsigned
                        // storage here so a later I8 use cannot sign-extend bit31.
                        // Signed managed consumers still request their own view.
                        type = instruction.NativeArithmeticSize == 4
                            ? method.AppContext.SystemTypes.SystemUInt32Type : method.AppContext.SystemTypes.SystemInt64Type;
                }
                else if (instruction is {OpCode: OpCode.Move, Operands: [_, LocalVariable source]}
                    && Integral(source.Type) && StableAt(source, instruction)
                    && (instruction.NativeRegisterCopySize == TypeSizes.UnboxedSize(source.Type!, method.AppContext.Binary.PointerSizeBytes)
                        || instruction.Index == -1 && instruction.NativeRegisterCopySize == 0)
                    && instruction.NativeReadSize == 0 && instruction.NativeWriteSize == 0)
                    type = source.Type;
                else if (instruction is {OpCode: OpCode.Move, Operands: [_, FieldReference field]}
                    && Integral(field.Field.FieldType) && instruction.NativeWriteSize == 0
                    && instruction.NativeReadSize == TypeSizes.UnboxedSize(field.Field.FieldType, method.AppContext.Binary.PointerSizeBytes))
                    type = field.Field.FieldType;
                if (type == null) continue;
                if (!safeResults.TryGetValue(result, out var safe))
                    safeResults[result] = safe = SafeResult(result, instruction);
                if (!safe) continue;
                result.Type = type;
                changed = true;
                changes++;
            }
        }
        return changes;
    }
}
