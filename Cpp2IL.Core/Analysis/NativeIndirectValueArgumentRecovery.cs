using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// AAPCS64 B.4 passes a non-homogeneous composite larger than sixteen bytes
// through the address of a caller-owned copy. CIL still takes its VALUE.
// Complete Android primary3061 and actual CFG3062 exhibit this distinction.
// This pass never assigns a type to unknown storage or rewrites a memcpy.
public static class NativeIndirectValueArgumentRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph
            || !graph.Instructions.Any(i => i.IsCall && i.Operands[0] is MethodAnalysisContext
                && i.Operands.Any(o => o is AddressOf { Target: LocalVariable { Type: not null } }))
            || !CheckedUnboxRecovery.Supports(method.AppContext)) return 0;
        return graph.Instructions.Sum(call => Rewrite(method, call, true));
    }

    internal static int Rewrite(MethodAnalysisContext method, Instruction call, bool reviewedImage)
    {
        if (!reviewedImage || method.ControlFlowGraph is not { } graph
            || call.OpCode is not (OpCode.Call or OpCode.CallVoid)
            || call.Operands.Count == 0 || call.Operands[0] is not MethodAnalysisContext target
            || !ReferenceEquals(target.AppContext, method.AppContext)
            || graph.Blocks.Sum(b => b.Instructions.Count(i => ReferenceEquals(i, call))) != 1)
            return 0;
        var first = (call.OpCode == OpCode.Call ? 2 : 1) + (target.IsStatic ? 0 : 1);
        if (call.Operands.Count < first + target.Parameters.Count) return 0;
        var changed = 0;
        for (var ordinal = 0; ordinal < target.Parameters.Count; ordinal++)
        {
            if (call.Operands[first + ordinal] is not AddressOf { Target: LocalVariable local }
                || local.Type is not { } type || !method.Locals.Contains(local)
                || local.IsThis || local.IsMethodInfo || local.IsReturnBuffer
                || !TrivialConstructorRecovery.SameType(type, target.Parameters[ordinal].ParameterType)
                || !IsIndirectAggregate(type)) continue;
            call.SetOperand(first + ordinal, local);
            changed++;
        }
        return changed;
    }

    internal static bool IsIndirectAggregate(TypeAnalysisContext type)
    {
        if (!type.IsValueType || TypeSizes.IsScalarValueType(type)
            || type.HasAnyGenericParameters() || Arm64HfaLayout.Fields(type) != null
            || TypeSizes.UnboxedSize(type, 8) is <= 16 or > 4096) return false;
        // Positively establish a non-floating scalar leaf. A failed HFA test
        // alone is insufficient: an unknown layout or HVA must not qualify.
        // Native vector intrinsics are outside this reviewed IL2CPP contract.
        var seen = new HashSet<TypeAnalysisContext>();
        var nonFloating = false;
        bool Inspect(TypeAnalysisContext current, int depth)
        {
            if (depth > 12 || current.FullName.StartsWith("System.Runtime.Intrinsics.")
                || current.FullName.StartsWith("System.Numerics.Vector")
                || current.FullName.StartsWith("Unity.Burst.Intrinsics.")) return false;
            if (TypeSizes.IsScalarValueType(current))
            {
                nonFloating |= !BaseCallingConventionResolver.IsFloatingPoint(current);
                return true;
            }
            if (!current.IsValueType || current.HasAnyGenericParameters() || !seen.Add(current))
                return false;
            var fields = current.Fields.Where(f => !f.IsStatic).ToArray();
            var valid = fields.Length > 0 && fields.All(f => Inspect(f.FieldType, depth + 1));
            seen.Remove(current);
            return valid;
        }
        return Inspect(type, 0) && nonFloating;
    }
}
