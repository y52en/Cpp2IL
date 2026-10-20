using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// The complete native Object constructor must have already been proven empty.
// Only the current instance's direct Object-base call is redundant in C#.
public static class EmptyObjectBaseConstructorRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4
            || method.AppContext.Binary.PointerSizeBytes != 8
            || method.AppContext.InstructionSet is not NewArmV8InstructionSet) return 0;
        return Recover(method);
    }

    internal static int Recover(MethodAnalysisContext method)
    {
        if (method.Name != ".ctor" || method.IsStatic || method.DeclaringType?.IsValueType != false
            || !TrivialConstructorRecovery.SameType(method.DeclaringType.BaseType, method.AppContext.SystemTypes.SystemObjectType)
            || method.ControlFlowGraph == null || method.ParameterLocals.Count == 0
            || !method.ParameterLocals[0].IsThis) return 0;
        var graph = method.ControlFlowGraph;
        var candidates = graph.Instructions.Where(i => i.OpCode == OpCode.CallVoid
            && i.Operands.Count == 2 && i.Operands[0] is MethodAnalysisContext target
            && target.Name == ".ctor" && !target.IsStatic && target.IsVoid && target.Parameters.Count == 0
            && TrivialConstructorRecovery.SameType(target.DeclaringType, method.AppContext.SystemTypes.SystemObjectType)
            && target.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey) is { IsNoOp: true }).ToArray();
        if (candidates.Length != 1) return 0;
        var call = candidates[0];
        var block = graph.Blocks.Single(b => b.Instructions.Contains(call));
        IOperand receiver = call.Operands[1];
        var seen = new HashSet<LocalVariable>();
        while (!ReferenceEquals(receiver, method.ParameterLocals[0]))
        {
            if (receiver is not LocalVariable local || !seen.Add(local) || seen.Count > 8) return 0;
            var definitions = graph.Instructions.Where(i => ReferenceEquals(i.Destination, local)).ToArray();
            if (definitions.Length != 1 || definitions[0].OpCode != OpCode.Move
                || definitions[0].Operands.Count != 2 || !block.Instructions.Contains(definitions[0])
                || block.Instructions.IndexOf(definitions[0]) >= block.Instructions.IndexOf(call)) return 0;
            receiver = definitions[0].Operands[1];
        }
        call.SetOperands([]);
        call.OpCode = OpCode.Nop;
        block.CalculateBlockType();
        return 1;
    }
}
