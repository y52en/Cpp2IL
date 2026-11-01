using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recover a division only after proving its complete signed-i32 domain.
// The native SMULL contract and every intermediate width remain mandatory.
internal static class SignedConstantDivisionRecovery
{
    internal static bool ProveDivisor(int magic, int shift, bool addDividend, out int divisor)
    {
        divisor = 0;
        if (shift is < 0 or > 31 || magic == 0 || (magic < 0) != addDividend) return false;
        var multiplier = new BigInteger(magic) + (addDividend ? BigInteger.One << 32 : 0);
        if (multiplier <= 0) return false;
        var scale = BigInteger.One << (32 + shift);
        var candidate = scale / multiplier + 1;
        if (candidate <= 1 || candidate > int.MaxValue) return false;
        var error = candidate * multiplier - scale;
        if (error <= 0) return false;
        BigInteger Maximum(BigInteger limit)
        {
            var q = BigInteger.DivRem(limit, candidate, out var remainder);
            var last = q * error + remainder * multiplier;
            return q == 0 ? last : BigInteger.Max(last, (q - 1) * error + (candidate - 1) * multiplier);
        }
        // For n>=0: floor(n*M/K)=floor(n/d) iff all residuals are <K.
        // For n=-a<0: -ceil(a*M/K)+1=-floor(a/d) iff 0<residual<=K.
        // Residuals increase within each quotient interval and between complete
        // intervals. These exact extrema cover every input, including INT_MIN.
        if (Maximum(int.MaxValue) >= scale || Maximum(BigInteger.One << 31) > scale) return false;
        divisor = (int)candidate; return true;
    }

    static int Width(TypeAnalysisContext? type) => type?.FullName switch
    {
        "System.Int32" or "System.UInt32" => 4,
        "System.Int64" or "System.UInt64" => 8,
        _ => 0,
    };

    internal static bool Rewrite(MethodAnalysisContext method, Instruction root)
    {
        if (method.ControlFlowGraph is not {} cfg || root is not
            { OpCode: OpCode.Add, NativeArithmeticSize: 4, Operands: [LocalVariable result, _, _] }
            || Width(result.Type) != 4) return false;
        var homes = cfg.Blocks.Where(b => b.Instructions.Contains(root)).ToArray();
        if (homes.Length != 1) return false;
        var groups = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var defs = groups.Where(g => g.Value.Length == 1).ToDictionary(g => g.Key, g => g.Value[0]);
        if (!defs.TryGetValue(result, out var resultDef) || !ReferenceEquals(resultDef, root)) return false;
        foreach (var swapped in new[] { false, true })
        {
            var trace = new HashSet<Instruction>();
            IOperand Unwrap(IOperand operand, int width = 4)
            {
                var seen = new HashSet<LocalVariable>();
                while (operand is LocalVariable local && seen.Add(local) && defs.TryGetValue(local, out var def))
                {
                    if (def is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }
                        && Width(local.Type) >= width && Width(source.Type) >= width
                        && (def.NativeRegisterCopySize == 0 || def.NativeRegisterCopySize >= width))
                    { trace.Add(def); operand = source; continue; }
                    if (def is { OpCode: OpCode.NumericConvert,
                            Operands: [_, TypeAnalysisContext target, TypeAnalysisContext from, var value] }
                        && Width(target) >= width && Width(target) is 4 or 8 && Width(target) == Width(from)
                        && def.NativeArithmeticSize == Width(target))
                    { trace.Add(def); operand = value; continue; }
                    break;
                }
                return operand;
            }
            Instruction? Def(IOperand value, int width = 4)
            {
                if (Unwrap(value, width) is not LocalVariable local || !defs.TryGetValue(local, out var found)) return null;
                trace.Add(found); return found;
            }
            bool Same(IOperand left, IOperand right) => ReferenceEquals(Unwrap(left), Unwrap(right));
            (LocalVariable Input, int Magic)? High(IOperand value)
            {
                if (Def(value) is not { OpCode: OpCode.ShiftRightUnsigned, NativeArithmeticSize: 8,
                        Operands: [_, var wide, Immediate { Value: 32 }] }
                    || Def(wide, 8) is not { OpCode: OpCode.Multiply, NativeArithmeticSize: 8,
                        NativeMultiplyInputSize: 4, NativeMultiplySigned: true, Operands: [_, var a, var b] }) return null;
                a = Unwrap(a); b = Unwrap(b);
                if (a is Immediate) (a, b) = (b, a);
                return a is LocalVariable input && Width(input.Type) is 4 or 8 && b is Immediate magic
                    ? (input, unchecked((int)magic.Value)) : null;
            }
            var quotient = swapped ? root.Operands[2] : root.Operands[1];
            var correction = swapped ? root.Operands[1] : root.Operands[2];
            if (Def(correction) is not { OpCode: OpCode.ShiftRightUnsigned, NativeArithmeticSize: 4,
                    Operands: [_, var correctionInput, Immediate { Value: 31 }] }) continue;
            var shifted = Def(quotient); var shift = 0; var adjusted = quotient;
            if (shifted is { OpCode: OpCode.ShiftRight, NativeArithmeticSize: 4,
                    Operands: [_, var beforeShift, Immediate amount] })
            {
                if (amount.Value is < 0 or > 31) continue;
                shift = (int)amount.Value; adjusted = beforeShift;
            }
            if (!Same(adjusted, correctionInput)) continue;
            (LocalVariable Input, int Magic)? product = null; var addDividend = false;
            if (Def(adjusted) is { OpCode: OpCode.Add, NativeArithmeticSize: 4, Operands: [_, var a, var b] })
            {
                var first = High(a);
                if (first is {} f && Same(f.Input, b)) product = first;
                else { var second = High(b); if (second is {} s && Same(s.Input, a)) product = second; }
                addDividend = true;
            }
            else product = High(adjusted);
            if (product is not {} matched || !ProveDivisor(matched.Magic, shift, addDividend, out var divisor)) continue;
            var input = matched.Input;
            if (!method.Locals.Contains(input) && !method.ParameterLocals.Contains(input)) continue;
            if (groups.TryGetValue(input, out var writes))
            {
                if (writes.Length != 1 || !ForwardNullCheckRecovery.DefinitionDominates(cfg, writes[0], root)) continue;
            }
            else if (!method.ParameterLocals.Contains(input)) continue;
            bool AddressTaken(IOperand operand) => operand switch
            {
                AddressOf address => ForwardNullCheckRecovery.Uses(address.Target, input),
                MemoryOperand memory => memory.Base != null && AddressTaken(memory.Base)
                    || memory.Index != null && AddressTaken(memory.Index),
                ArrayAccess array => AddressTaken(array.Index),
                _ => false,
            };
            if (cfg.Instructions.SelectMany(i => i.Operands).Any(AddressTaken)
                || trace.Any(i => !ForwardNullCheckRecovery.DefinitionDominates(cfg, i, root))) continue;
            var types = method.AppContext.SystemTypes;
            var signed = new LocalVariable("division_input_" + root.Index, new(null, "division_input_" + root.Index), types.SystemInt32Type);
            var divided = new LocalVariable("division_result_" + root.Index, new(null, "division_result_" + root.Index), types.SystemInt32Type);
            method.Locals.AddRange([signed, divided]);
            var at = homes[0].Instructions.IndexOf(root);
            homes[0].Instructions.Insert(at, new(root.Index, OpCode.NumericConvert, signed, types.SystemInt32Type, input.Type!, input)
                { NativeArithmeticSize = 4, NativeIntegerSourceView = true });
            homes[0].Instructions.Insert(at + 1, new(root.Index, OpCode.Divide, divided, signed, new Immediate(divisor))
                { NativeArithmeticSize = 4 });
            root.OpCode = OpCode.NumericConvert;
            root.SetOperands(result, result.Type!, types.SystemInt32Type, divided);
            return true;
        }
        return false;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            || method.ControlFlowGraph is not {} cfg) return 0;
        var changed = cfg.Instructions.Where(i => i.OpCode == OpCode.Add).ToArray().Count(i => Rewrite(method, i));
        if (changed != 0) DeadCodeEliminator.Run(method);
        return changed;
    }
}
