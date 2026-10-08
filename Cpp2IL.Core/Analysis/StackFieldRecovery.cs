using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A by-address native struct write does not define each synthetic stack slot in
// SSA. Reconnect ONLY otherwise-undefined slot reads to metadata-known fields.
// Assigned slots, whole-value writes, ambiguous storage and unknown calls remain
// untouched. This is not permission to invent values or clear a structure.
public static class StackFieldRecovery
{
    private static readonly HashSet<string> Scalars = new(StringComparer.Ordinal)
    {
        "System.Boolean","System.Byte","System.SByte","System.Char","System.Int16","System.UInt16",
        "System.Int32","System.UInt32","System.Int64","System.UInt64","System.Single","System.Double",
        "System.IntPtr","System.UIntPtr"
    };
    private sealed record Writer(Instruction Call, Block Block, LocalVariable Storage, int Offset);

    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = new HashSet<LocalVariable>(graph.Instructions.Select(i=>i.Destination).OfType<LocalVariable>());
        var writers = new List<Writer>();
        foreach (var block in graph.Blocks)
        foreach (var call in block.Instructions)
        {
            if (!call.IsCall || call.Operands[0] is not MethodAnalysisContext target) continue;
            var first = call.OpCode == OpCode.CallVoid ? 1 : 2;
            if (!target.IsStatic && target.DeclaringType?.IsValueType == true && call.Operands.Count > first
                && call.Operands[first] is AddressOf { Target: LocalVariable storage }
                && storage.Type == target.DeclaringType && TryOffset(storage,out var offset))
                writers.Add(new(call,block,storage,offset));
            if (call.Destination is LocalVariable result && result.Type?.IsValueType == true
                && result.Type == target.ReturnType && TryOffset(result,out var resultOffset))
                writers.Add(new(call,block,result,resultOffset));
        }
        if (writers.Count == 0) return false;
        DominatorInfo? dominance = null;
        var changed = false;
        foreach (var block in graph.Blocks)
        foreach (var instruction in block.Instructions)
        for (var i=0;i<instruction.Operands.Count;i++)
        {
            if (instruction.Operands[i] is not LocalVariable local || definitions.Contains(local)
                || ReferenceEquals(instruction.Destination,local) || !TryOffset(local,out var offset)) continue;
            var matches = new List<FieldReference>();
            foreach (var writer in writers)
            {
                // Field zero is indistinguishable from an entire struct value at
                // the same address. Do not project it without width evidence.
                var delta = offset - writer.Offset;
                if (delta <= 0) continue;
                var fields = writer.Storage.Type!.Fields.Where(f=>!f.IsStatic && f.Offset == delta).ToArray();
                if (fields.Length != 1 || fields[0].FieldType.IsValueType && !fields[0].FieldType.IsEnumType
                    && !Scalars.Contains(fields[0].FieldType.FullName)) continue;
                var field = fields[0];
                if (local.Type != null && local.Type != field.FieldType) continue;
                var preceding = writer.Block == block
                    ? block.Instructions.IndexOf(writer.Call) < block.Instructions.IndexOf(instruction)
                    : (dominance ??= new DominatorInfo(graph)).Dominates(writer.Block,block);
                if (!preceding) continue;
                if (!matches.Any(m=>m.Field == field && ReferenceEquals(m.Local,writer.Storage)))
                    matches.Add(new(field,writer.Storage,delta));
            }
            if (matches.Count != 1) continue;
            instruction.SetOperand(i,matches[0]); changed = true;
        }
        return changed;
    }

    private static bool TryOffset(LocalVariable local,out int offset)
    {
        offset = 0;
        var name = local.Register.Name;
        if (!name.StartsWith("stack_",StringComparison.Ordinal)) return false;
        var text = name.Substring(6);
        var negative = text.StartsWith("-",StringComparison.Ordinal);
        if (negative) text = text.Substring(1);
        if (!int.TryParse(text,NumberStyles.AllowHexSpecifier,CultureInfo.InvariantCulture,out var value) || value < 0) return false;
        offset = negative ? -value : value;
        return true;
    }
}
