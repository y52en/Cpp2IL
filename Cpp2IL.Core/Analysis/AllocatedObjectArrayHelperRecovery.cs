using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Only a fresh, exact object[] allocation: never a covariantly typed input.
// Every managed reference fits this element type, so the outlined covariance
// check cannot throw. Keep the store's null/bounds behavior as managed stelem.
public static class AllocatedObjectArrayHelperRecovery
{
    private const string CheckHash = "d898def3db1752bedc0cc2403fb4d7db268ad38c58c4337ae3f339be86640714";
    private const string StoreHash = "480f2329290258c749565b9d70a565d672ac44da1357fffde4acdc92e7115234";
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, int>> Proofs = new();

    internal static int ClassifyHelperBytes(byte[] bytes)
    {
        if (bytes.Length is not (64 or 80)) return 0;
        using var sha = SHA256.Create();
        var hash = string.Concat(sha.ComputeHash(bytes).Select(b => b.ToString("x2")));
        return bytes.Length == 64 && hash == CheckHash ? 1 : bytes.Length == 80 && hash == StoreHash ? 2 : 0;
    }

    private static int Prove(MethodAnalysisContext method, ulong address)
        => Proofs.GetValue(method.AppContext, _ => new()).GetOrAdd(address, candidate =>
        {
            try
            {
                var binary = method.AppContext.Binary; var offset = checked((int)binary.MapVirtualAddressToRaw(candidate));
                var content = binary.GetRawBinaryContent();
                if (offset < 0 || offset > content.Length - 64) return 0;
                if (ClassifyHelperBytes(content.Slice(offset, 64).ToArray()) == 1) return 1;
                return offset <= content.Length - 80 ? ClassifyHelperBytes(content.Slice(offset, 80).ToArray()) : 0;
            }
            catch (Exception) { return 0; }
        });

    internal static bool TryRewrite(ISILControlFlowGraph cfg, Instruction call,
        Dictionary<LocalVariable, Instruction> definitions, int kind)
    {
        if (kind is not (1 or 2) || call.OpCode is not (OpCode.Call or OpCode.CallVoid)) return false;
        var first = call.OpCode == OpCode.Call ? 2 : 1;
        if (call.Operands.Count < first + (kind == 1 ? 2 : 3)
            || call.Operands[first] is not LocalVariable array) return false;
        if (call.OpCode == OpCode.Call && (call.Destination is not LocalVariable result
            || cfg.Instructions.Any(i => !ReferenceEquals(i, call) && i.Operands.Any(o => ForwardNullCheckRecovery.Uses(o, result))))) return false;
        IOperand Resolve(IOperand operand)
        {
            var copies = new HashSet<LocalVariable>();
            while (operand is LocalVariable local && copies.Add(local) && definitions.TryGetValue(local, out var definition)
                   && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable or Immediate or StringLiteral] })
                operand = definition.Operands[1];
            return operand;
        }
        var root = array; var seen = new HashSet<LocalVariable>();
        while (seen.Add(root) && definitions.TryGetValue(root, out var copy)
               && copy is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }) root = source;
        if (!definitions.TryGetValue(root, out var allocation)
            || allocation is not { OpCode: OpCode.NewArr,
                Operands: [_, SzArrayTypeAnalysisContext { ElementType.FullName: "System.Object" } actualType, _] }
            || !ReferenceEquals(actualType.ElementType, actualType.AppContext.SystemTypes.SystemObjectType)
            || !ForwardNullCheckRecovery.DefinitionDominates(cfg, allocation, call)
            || array.Type != null && !ReferenceEquals(array.Type, actualType)) return false;
        var value = Resolve(call.Operands[first + (kind == 1 ? 1 : 2)]);
        if (value is not (Immediate { Value: 0 } or StringLiteral)
            && value is not LocalVariable { Type: { IsValueType: false, Type: Il2CppTypeEnum.IL2CPP_TYPE_CLASS
                or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or Il2CppTypeEnum.IL2CPP_TYPE_STRING
                or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST } }) return false;
        if (kind == 1)
        {
            call.OpCode = OpCode.Nop; call.SetOperands(); return true;
        }
        var index = Resolve(call.Operands[first + 1]);
        if (index is LocalVariable
            && InterfaceDispatchRecovery.ResolveDispatchOperand(index, definitions) is Immediate materialized)
            index = materialized;
        if (index is not (Immediate { Value: >= int.MinValue and <= int.MaxValue }
            or LocalVariable { Type.FullName: "System.Int32" })) return false;
        array.Type ??= actualType;
        call.OpCode = OpCode.Move; call.SetOperands(new ArrayAccess(array, index), value); call.NativeWriteSize = 8;
        return true;
    }

    internal static bool TrimProvenPadding(Instruction call, int realArguments)
    {
        if (realArguments is < 1 or > 3 || call.OpCode is not (OpCode.Call or OpCode.CallVoid)) return false;
        var expected = realArguments + (call.OpCode == OpCode.Call ? 2 : 1);
        if (call.Operands.Count <= expected) return false;
        call.SetOperands(call.Operands.Take(expected).ToList());
        return true;
    }

    public static int TrimKnownHelperPadding(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4) return 0;
        var changed = 0;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [Immediate helper, ..] }) continue;
            var kind = Prove(method, helper.UnsignedValue);
            var count = kind == 1 ? 2 : kind == 2 ? 3 : ForwardNullCheckRecovery.Prove(method, helper.UnsignedValue) ? 1 : 0;
            if (count != 0 && TrimProvenPadding(instruction, count)) changed++;
        }
        return changed;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4) return 0;
        var cfg = method.ControlFlowGraph!;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var changed = 0;
        var trace = Environment.GetEnvironmentVariable("CPP2IL_TRACE_OBJECT_ARRAY_RVA") is { } requested
            && string.Equals(requested, method.UnderlyingPointer.ToString("X"), StringComparison.OrdinalIgnoreCase);
        foreach (var block in cfg.Blocks)
        foreach (var instruction in block.Instructions)
            if (instruction is { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [Immediate helper, ..] })
            {
                var kind = Prove(method, helper.UnsignedValue);
                if (trace && helper.Value is 0xa621ec or 0xa6222c)
                {
                    Console.Error.WriteLine("OBJECT_ARRAY helper-kind=" + kind + " " + instruction);
                    foreach (var operand in instruction.Operands.OfType<LocalVariable>())
                    {
                        var value = operand; var seen = new HashSet<LocalVariable>();
                        while (seen.Add(value))
                        {
                            definitions.TryGetValue(value, out var definition);
                            Console.Error.WriteLine("OBJECT_ARRAY value=" + value + " type-identity="
                                + (value.Type == null ? 0 : RuntimeHelpers.GetHashCode(value.Type)) + " definition=" + definition);
                            if (definition is { OpCode: OpCode.NewArr, Operands: [_, var allocationType, _] })
                                Console.Error.WriteLine("OBJECT_ARRAY allocation-type-identity=" + RuntimeHelpers.GetHashCode(allocationType));
                            if (definition is not { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }) break;
                            value = source;
                        }
                    }
                }
                if (TryRewrite(cfg, instruction, definitions, kind)) { block.CalculateBlockType(); changed++; }
            }
        return changed;
    }
}
