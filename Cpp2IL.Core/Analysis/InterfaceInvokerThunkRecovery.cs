using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Non-inlined interface invoker: slot, declaring interface, object. Complete
// original C is archived in evidence/round404/interface_invoke_no_arguments.c.
// This first profile supports only zero-argument, reference-returning members.
public static class InterfaceInvokerThunkRecovery
{
    private const int HelperLength = 124;
    private const string HelperHash = "3b3d5725357b5423ab94a52323e392f3ec4ace8f572d0c9f3f2ad003b8985389";
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, bool>> Proofs = new();

    internal static bool MatchesHelperBytes(byte[] bytes)
    {
        if (bytes.Length != HelperLength) return false;
        using var sha = SHA256.Create();
        return string.Concat(sha.ComputeHash(bytes).Select(b => b.ToString("x2"))) == HelperHash;
    }

    private static bool IsProvenHelper(MethodAnalysisContext method, ulong address)
        => Proofs.GetValue(method.AppContext, _ => new()).GetOrAdd(address, candidate =>
        {
            try
            {
                var binary = method.AppContext.Binary;
                var offset = checked((int)binary.MapVirtualAddressToRaw(candidate));
                var content = binary.GetRawBinaryContent();
                return offset >= 0 && offset <= content.Length - HelperLength
                    && MatchesHelperBytes(content.Slice(offset, HelperLength).ToArray());
            }
            catch (Exception) { return false; }
        });

    internal static MethodAnalysisContext? Bind(TypeAnalysisContext owner, int slot)
    {
        var definition = owner is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : owner;
        if (!definition.IsInterface || slot < 0 || slot > ushort.MaxValue) return null;
        var methods = definition.Methods.Where(m => m.Definition?.slot == slot).Take(2).ToArray();
        if (methods.Length != 1) return null;
        MethodAnalysisContext target = owner is GenericInstanceTypeAnalysisContext generic
            ? new ConcreteGenericMethodAnalysisContext(methods[0], generic.GenericArguments, []) : methods[0];
        if (target.IsStatic || target.IsVoid || target.Parameters.Count != 0 || target.GenericParameters.Count != 0
            || target.ReturnType.IsValueType || target.ReturnType.HasAnyGenericParameters()
            || target.ReturnType.Type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                or Il2CppTypeEnum.IL2CPP_TYPE_STRING or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
                or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST)) return null;
        return target;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4) return 0;
        var cfg = method.ControlFlowGraph!;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var changed = 0;
        foreach (var instruction in cfg.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Call,
                    Operands: [Immediate helper, LocalVariable result, var slotOperand, var ownerOperand, LocalVariable receiver, ..] }
                || !IsProvenHelper(method, helper.UnsignedValue)
                || InterfaceDispatchRecovery.ResolveDispatchOperand(slotOperand, definitions) is not Immediate { Value: >= 0 and <= ushort.MaxValue } slot
                || InterfaceDispatchRecovery.ResolveDispatchOperand(ownerOperand, definitions) is not TypeAnalysisContext owner
                || Bind(owner, (int)slot.Value) is not { } target) continue;
            instruction.SetOperands(target, result, receiver);
            instruction.NativeVirtualDispatch = true;
            result.Type ??= target.ReturnType;
            changed++;
        }
        return changed;
    }
}
