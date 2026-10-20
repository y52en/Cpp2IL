using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// A native zero result is default(T) only for this exact shared enum entry,
// not a global declaration that every open T is a four-byte value type.
public static class SharedEnumDefaultReturnRecovery
{
    internal static bool HasUniformEnumAliases(MethodAnalysisContext method, IReadOnlyList<MethodAnalysisContext> aliases)
    {
        if (method is ConcreteGenericMethodAnalysisContext
            || method.ReturnType is not GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_MVAR } parameter
            || !ReferenceEquals(parameter.Owner, method) || !method.GenericParameters.Contains(parameter)
            || aliases.Count < 2 || aliases.Distinct().Count() != aliases.Count
            || aliases.Count(m => ReferenceEquals(m, method)) != 1) return false;
        TypeAnalysisContext? underlying = null;
        foreach (var alias in aliases)
        {
            if (ReferenceEquals(alias, method)) continue;
            if (alias is not ConcreteGenericMethodAnalysisContext concrete || !ReferenceEquals(concrete.BaseMethodContext, method)
                || !alias.ReturnType.IsEnumType || alias.ReturnType.EnumUnderlyingType is not { Type: Il2CppTypeEnum.IL2CPP_TYPE_I4 or Il2CppTypeEnum.IL2CPP_TYPE_U4 } scalar
                || underlying != null && !ReferenceEquals(underlying, scalar)) return false;
            underlying = scalar;
        }
        return underlying != null;
    }

    internal static int Rewrite(MethodAnalysisContext method, IReadOnlyList<MethodAnalysisContext> aliases)
    {
        if (!HasUniformEnumAliases(method, aliases)) return 0;
        var count = 0;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction is { OpCode: OpCode.Return, Operands: [Immediate { Value: 0 }] })
            {
                instruction.SetOperand(0, new DefaultStructValue(method.ReturnType)); count++;
            }
        return count;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4
            || method.UnderlyingPointer == 0
            || !method.AppContext.MethodsByAddress.TryGetValue(method.UnderlyingPointer, out var aliases)) return 0;
        return Rewrite(method, aliases);
    }
}
