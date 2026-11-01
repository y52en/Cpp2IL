using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

/// <summary>Recover dispatch through MethodInfo.methodPointer, not an arbitrary callback.</summary>
public static class MethodInfoTailRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4
            || app.Binary.PointerSizeBytes != 8 || app.InstructionSet is not NewArmV8InstructionSet)
            return false;
        return Recover(method);
    }

    internal static bool Recover(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = graph.Instructions.Where(i => i.OpCode == OpCode.Move && i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var resolver = method.AppContext.InstructionSet.CallingConventionResolver;
        if (resolver is not Arm64CallingConventionResolver) return false;
        var changed = false;
        foreach (var block in graph.Blocks)
        {
          foreach (var jump in block.Instructions.ToArray())
          {
            var tail = jump.OpCode == OpCode.IndirectJump;
            if (jump.OpCode is not (OpCode.IndirectJump or OpCode.IndirectCall) || jump.Operands.Count != 18
                || tail && !ReferenceEquals(jump, block.Instructions.Last()))
                continue; // target, stale return register, X0-X7, V0-V7
            var pointer = jump.Operands[0];
            if (pointer is LocalVariable local && definitions.TryGetValue(local, out var load))
            {
                // Require a local, preceding SSA definition, not a load from an unrelated branch.
                if (!block.Instructions.Contains(load) || block.Instructions.IndexOf(load) >= block.Instructions.IndexOf(jump))
                    continue;
                pointer = load.Operands[1];
            }
            if (pointer is not MemoryOperand { Addend: 0, Index: null, Scale: 0 } memory
                || Info(memory.Base) is not { RepresentedMethod: { } target } info)
                continue;
            // Exact return identity makes the tail result ABI identical, including open T.
            // Never invent a conversion, discarded return value, or hidden-buffer remapping.
            if (tail && !TrivialConstructorRecovery.SameType(method.ReturnType, target.ReturnType) || resolver.ReturnsViaHiddenBuffer(target)
                || target.Parameters.Any(p => p.ParameterType is GenericParameterTypeAnalysisContext
                    || p.ParameterType.IsValueType && !BaseCallingConventionResolver.IsFloatingPoint(p.ParameterType)
                    && !IsSupportedWordValue(p.ParameterType)))
                continue;
            // Unknown indirect calls define X0 only in upstream ISIL. A float,
            // HFA, aggregate or open-T result requires SSA repair of the actual
            // return register, not a rename of that X0 local.
            var oldResult = jump.Destination as LocalVariable;
            if (!tail && (!target.IsVoid && (target.ReturnType is GenericParameterTypeAnalysisContext genericReturn && !HasReferenceOnlyConstraint(genericReturn)
                    || resolver.ReturnRegister(target).Name != "X0"
                    || target.ReturnType.IsValueType && !IsSupportedWordValue(target.ReturnType)
                    || oldResult?.Register.Name != "X0")
                || target.IsVoid && oldResult != null && graph.Instructions.Any(i => i.Sources.Contains(oldResult))))
                continue;
            var slots = resolver.ResolveForManaged(target);
            var args = new List<IOperand>();
            var valid = true;
            foreach (var slot in slots)
            {
                if (slot is not Register register || register.Name.Length != 2
                    || register.Name[1] < '0' || register.Name[1] > '7'
                    || register.Name[0] is not ('X' or 'V')) { valid = false; break; }
                var operand = jump.Operands[2 + register.Name[1] - '0' + (register.Name[0] == 'V' ? 8 : 0)];
                // Folding may replace a physical argument by its constant/MethodInfo.
                // Copy propagation changes a value's register identity, not
                // its argument slot. Permit that only when the lifter proved
                // the raw ordered snapshot and all structural edits retained it.
                if (operand is LocalVariable lv && (lv.Register.Name == register.Name
                        || jump.HasArm64IndirectArgumentSnapshot)
                    || register.Name[0] == 'X' && operand is Immediate
                    || register.Name[0] == 'V' && operand is FloatLiteral or DoubleLiteral
                    || Info(operand) is { } hidden && ReferenceEquals(hidden.RepresentedMethod, target))
                    args.Add(operand);
                else { valid = false; break; }
            }
            if (!valid || args.Count == 0 || Info(args.Last()) is not { } passedInfo
                || !ReferenceEquals(passedInfo.RepresentedMethod, info.RepresentedMethod)) continue;
            LocalVariable? result = null;
            var operands = new List<IOperand> { target };
            if (!target.IsVoid)
            {
                result = tail ? new LocalVariable("methodInfoTailResult_" + jump.Index,
                    new Register(null, "method_info_tail_result_" + jump.Index), target.ReturnType) : oldResult!;
                result.Type = target.ReturnType;
                if (tail) method.Locals.Add(result);
                operands.Add(result);
            }
            operands.AddRange(args);
            jump.SetOperands(operands);
            jump.OpCode = target.IsVoid ? OpCode.CallVoid : OpCode.Call;
            if (tail)
            {
                block.AddInstruction(new Instruction(-1, OpCode.Return,
                    target.IsVoid ? [] : new List<IOperand> { result! }));
                block.CalculateBlockType();
            }
            changed = true;
          }
        }
        return changed;
    }

    internal static bool IsSupportedWordValue(TypeAnalysisContext type)
    {
        if (type.IsEnumType)
        {
            // Only metadata-proven CLI integer enum storage. Never substitute
            // a guessed int for an enum, recurse through malformed enum types,
            // or treat an arbitrary small struct as a scalar.
            return type.EnumUnderlyingType is { } underlying
                && !ReferenceEquals(type, underlying) && !underlying.IsEnumType
                && underlying.Type is Il2CppTypeEnum.IL2CPP_TYPE_I1 or Il2CppTypeEnum.IL2CPP_TYPE_U1
                    or Il2CppTypeEnum.IL2CPP_TYPE_I2 or Il2CppTypeEnum.IL2CPP_TYPE_U2
                    or Il2CppTypeEnum.IL2CPP_TYPE_I4 or Il2CppTypeEnum.IL2CPP_TYPE_U4
                    or Il2CppTypeEnum.IL2CPP_TYPE_I8 or Il2CppTypeEnum.IL2CPP_TYPE_U8;
        }
        return ReferenceEquals(type, type.AppContext.SystemTypes.SystemIntPtrType)
            || ReferenceEquals(type, type.AppContext.SystemTypes.SystemUIntPtrType)
            || type.Type is Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN or Il2CppTypeEnum.IL2CPP_TYPE_CHAR
                or Il2CppTypeEnum.IL2CPP_TYPE_I1 or Il2CppTypeEnum.IL2CPP_TYPE_U1
                or Il2CppTypeEnum.IL2CPP_TYPE_I2 or Il2CppTypeEnum.IL2CPP_TYPE_U2
                or Il2CppTypeEnum.IL2CPP_TYPE_I4 or Il2CppTypeEnum.IL2CPP_TYPE_U4
                or Il2CppTypeEnum.IL2CPP_TYPE_I8 or Il2CppTypeEnum.IL2CPP_TYPE_U8
                or Il2CppTypeEnum.IL2CPP_TYPE_I or Il2CppTypeEnum.IL2CPP_TYPE_U;
    }

    internal static bool HasReferenceOnlyConstraint(GenericParameterTypeAnalysisContext parameter)
    {
        var flags = parameter.Attributes;
        if ((flags & System.Reflection.GenericParameterAttributes.NotNullableValueTypeConstraint) != 0) return false;
        if ((flags & System.Reflection.GenericParameterAttributes.ReferenceTypeConstraint) != 0) return true;
        // Interface/new()/Object/ValueType/Enum constraints do not establish an
        // X0 reference return. Retain the original T, not its class bound.
        return parameter.ConstraintTypes.Any(t => !t.IsInterface && !t.IsValueType
            && t.Type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_STRING or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
            && t.FullName is not ("System.Object" or "System.ValueType" or "System.Enum"));
    }

    private static RuntimeMethodInfoAnalysisContext? Info(IOperand? operand) => operand switch
    {
        RuntimeMethodInfoAnalysisContext info => info,
        LocalVariable { Type: RuntimeMethodInfoAnalysisContext info } => info,
        _ => null
    };
}
