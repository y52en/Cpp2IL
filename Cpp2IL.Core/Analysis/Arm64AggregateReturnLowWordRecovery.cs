using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A native W comparison reads a four-byte view of a small ordinary X0/X1
// aggregate return. Proven X-register copies and LSR #32 preserve that view
// even when intermediate SSA locals were inferred to be UInt64.
// Preserve the actual call and every other aggregate consumer. No reinterpret
// cast, getter call, discarded upper lane or synthesized default is introduced.
public static class Arm64AggregateReturnLowWordRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes != 8
            || !CheckedUnboxRecovery.Supports(method.AppContext)
            || method.ControlFlowGraph is not {} graph) return 0;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);
        var changed = 0;
        foreach (var instruction in graph.Instructions.ToArray())
        {
            if (instruction.NativeComparisonSize != 4 || instruction.Operands.Count != 3
                || instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual
                    or OpCode.CheckLess or OpCode.CheckLessOrEqual
                    or OpCode.CheckGreater or OpCode.CheckGreaterOrEqual)) continue;
            for (var index = 1; index <= 2; index++)
            {
                if (instruction.Operands[index] is not LocalVariable value
                    || !TryResolveRegisterView(graph, definitions, instruction, value,
                        out var root, out var origin, out var offset)
                    || root.Type is not {} type
                    || !type.IsValueType || TypeSizes.IsScalarValueType(type)
                    || type.IsGenericInstance || type.HasAnyGenericParameters()
                    || type.Definition?.RawSizes == null
                    || TypeSizes.UnboxedSize(type, 8) is <= 4 or > 16
                    || Arm64HfaLayout.Fields(type) != null) continue;
                if (origin is not { OpCode: OpCode.Call, NativeVirtualDispatch: false,
                        Operands: [MethodAnalysisContext target, LocalVariable returned, ..] }
                    || !ReferenceEquals(returned, root) || root.Register.Name != "X0"
                    || target.Definition == null || target.UnderlyingPointer == 0
                    || origin.NativeDirectCallTarget != target.UnderlyingPointer
                    || !method.AppContext.MethodsByAddress.TryGetValue(target.UnderlyingPointer, out var aliases)
                    || !ProveReturnAliases(method, target, aliases)
                    || !TrivialConstructorRecovery.SameType(target.ReturnType, type)
                    || method.AppContext.InstructionSet.CallingConventionResolver!.ReturnsViaHiddenBuffer(target)) continue;
                var field = NestedFieldAccess.Find(type, root, offset, 4, method);
                if (field == null || field.Parent != null
                    || !ProveField(field.Field, method, instruction, offset)) continue;
                instruction.SetOperand(index, field);
                changed++;
            }
        }
        return changed;
    }

    // Trace native storage, not inferred managed spelling. Never retag a
    // producer or delete a conversion: other consumers retain their original
    // operations, and the existing SSA DCE removes only unused pure chains.
    internal static bool TryResolveRegisterView(ISILControlFlowGraph graph,
        Dictionary<LocalVariable, Instruction?> definitions, Instruction consumer,
        LocalVariable value, out LocalVariable root, out Instruction? origin, out int offset)
    {
        root = value; origin = null; offset = 0;
        var seen = new HashSet<LocalVariable>();
        while (seen.Add(root) && seen.Count <= 16
            && definitions.TryGetValue(root, out var definition) && definition != null)
        {
            // Check every def-use edge, including edges inside the chain.
            if (!ForwardNullCheckRecovery.DefinitionDominates(graph, definition, consumer)) return false;
            if (definition is { OpCode: OpCode.Call })
            { origin = definition; return true; }
            LocalVariable? source = null;
            if (definition is { OpCode: OpCode.Move, NativeReadSize: 0, NativeWriteSize: 0,
                    Operands: [LocalVariable, LocalVariable copied] }
                && (definition.NativeRegisterCopySize == 8 && RegisterPayload(root.Type) && RegisterPayload(copied.Type)
                    // Preserve existing whole-aggregate SSA copies. Scalar
                    // copies require a positive native eight-byte witness.
                    || definition.NativeRegisterCopySize == 0
                        && root.Type is { IsValueType: true } aggregate && !TypeSizes.IsScalarValueType(aggregate)
                        && TrivialConstructorRecovery.SameType(copied.Type, aggregate)))
                source = copied;
            else if (definition is { OpCode: OpCode.NumericConvert, NativeReadSize: 0, NativeWriteSize: 0,
                    NativeArithmeticSize: 8, Operands: [LocalVariable,
                        TypeAnalysisContext { FullName: "System.UInt64" },
                        TypeAnalysisContext { FullName: "System.UInt64" }, LocalVariable converted] }
                && root.Type?.FullName == "System.UInt64" && RegisterPayload(converted.Type))
                source = converted;
            else if (definition is { OpCode: OpCode.ShiftRightUnsigned, NativeReadSize: 0, NativeWriteSize: 0,
                    NativeArithmeticSize: 8, Operands: [LocalVariable, LocalVariable shifted, Immediate { Value: 32 }] }
                && offset == 0 && root.Type?.FullName == "System.UInt64"
                && shifted.Type?.FullName == "System.UInt64")
            { source = shifted; offset = 4; }
            if (source == null) return false;
            consumer = definition;
            root = source;
        }
        return false; // Phi, cycles, duplicate definitions or depth exhaustion.
    }

    private static bool RegisterPayload(TypeAnalysisContext? type) => type != null
        && (type.FullName is "System.Int64" or "System.UInt64"
            || type.IsValueType && !TypeSizes.IsScalarValueType(type)
                && !type.IsGenericInstance && !type.HasAnyGenericParameters());

    internal static bool ProveReturnAliases(MethodAnalysisContext caller, MethodAnalysisContext target,
        IReadOnlyList<MethodAnalysisContext> aliases)
    {
        // ICF aliases do not establish managed method identity. This pass
        // changes no call target or argument: prove only that EVERY registered
        // entry has the identical concrete managed return type and X0 ABI.
        // Different return types/layouts, missing metadata or hidden buffers
        // remain ambiguous even when their first fields look similar.
        var resolver = caller.AppContext.InstructionSet.CallingConventionResolver;
        if (resolver == null || aliases.Count == 0 || !aliases.Any(a => ReferenceEquals(a, target))
            || target.UnderlyingPointer == 0 || target.ReturnType.Definition == null
            || target.ReturnType.HasAnyGenericParameters()) return false;
        return aliases.All(alias => alias.Definition != null && !alias.IsVoid
            && alias.UnderlyingPointer == target.UnderlyingPointer
            && TrivialConstructorRecovery.SameType(alias.ReturnType, target.ReturnType)
            && !resolver.ReturnsViaHiddenBuffer(alias)
            && resolver.ReturnRegister(alias).Name == "X0");
    }

    internal static bool ProveField(FieldAnalysisContext field, MethodAnalysisContext caller, Instruction compare, int offset = 0)
    {
        var type = field.FieldType;
        if (type.IsEnumType) type = type.EnumUnderlyingType!;
        if (type == null || field.BackingData == null || field.IsStatic
            || offset is not (0 or 4) || field.Offset != offset
            || field.Attributes.HasFlag(FieldAttributes.Literal)
            || (field.Visibility != FieldAttributes.Public
                && !TrivialConstructorRecovery.SameType(field.DeclaringType, caller.DeclaringType))
            || type.FullName is not ("System.Int32" or "System.UInt32")) return false;
        // Relational operations must keep native signedness. Equality is the
        // same four-bit-byte comparison for either signed integral spelling.
        return compare.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
            || (compare.UnsignedComparison ? type.FullName == "System.UInt32" : type.FullName == "System.Int32");
    }
}
