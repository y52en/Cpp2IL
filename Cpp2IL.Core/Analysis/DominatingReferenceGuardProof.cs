using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Proves only that this existing consumer is reached on a non-null edge.
// Never removes or moves the earlier guard, its null branch, or its effects.
internal static class DominatingReferenceGuardProof
{
    internal static bool NonNullAt(MethodAnalysisContext method,LocalVariable source,Block consumer)
    {
        if(method.ControlFlowGraph is not {} graph || !graph.Blocks.Contains(consumer)
            || !InlineClassTestRecovery.StableSource(method,source,consumer))return false;
        var defs=graph.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var dominance=new DominatorInfo(graph);
        foreach(var guard in graph.Blocks) {
            if(ReferenceEquals(guard,consumer)||guard.Successors.Count!=2||guard.Successors.Distinct().Count()!=2
                || !dominance.Dominates(guard,consumer)
                || guard.Instructions.LastOrDefault() is not
                    {OpCode:OpCode.ConditionalJump,Operands:[Block target,LocalVariable flag]}
                || !guard.Successors.Contains(target))continue;
            var inverted=false;var seen=new HashSet<LocalVariable>();var condition=flag;
            while(seen.Count<8 && seen.Add(condition) && condition.Type?.FullName=="System.Boolean"
                && defs.TryGetValue(condition,out var predicate) && guard.Instructions.Contains(predicate)) {
                if(predicate is {OpCode:OpCode.Not,Operands:[_,LocalVariable previous]}) {
                    inverted=!inverted;condition=previous;continue;
                }
                if(predicate is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,Operands:[_,var a,var b]})break;
                if(!((ReferenceEquals(a,source)&&b is Immediate {Value:0})
                    ||(ReferenceEquals(b,source)&&a is Immediate {Value:0})))break;
                if(defs.TryGetValue(source,out var sourceWrite)
                    && !ForwardNullCheckRecovery.DefinitionDominates(graph,sourceWrite,predicate))break;
                var jumpsOnNull=(predicate.OpCode==OpCode.CheckEqual)!=inverted;
                var nonnull=jumpsOnNull?guard.Successors.Single(b=>!ReferenceEquals(b,target)):target;
                if(dominance.Dominates(nonnull,consumer))return true;
                break;
            }
        }
        return false;
    }
}
