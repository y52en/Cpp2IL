using System;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

// Resolve only a proven original metadata usage consumed by a native newobj.
// Do not rerun SSA-wide type inference over coalesced/reassigned locals.
public static class LateMetadataAllocationRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.AppContext.Binary is not ElfFile elf)return 0;
        return Recover(method,slot=>elf.IsGlobalOffsetTableEntry(slot)?elf.ReadPointerAtVirtualAddress(slot):null,
            address=>method.AppContext.LibCpp2IlContext.GetTypeGlobalByAddress(address) is { } native
                ?method.AppContext.ResolveIl2CppType(native):null);
    }

    internal static int Recover(MethodAnalysisContext method,Func<ulong,ulong?> readGot,
        Func<ulong,TypeAnalysisContext?> resolveType)
    {
        if(method.ControlFlowGraph is not { } graph)return 0;
        var definitions=graph.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).ToDictionary(g=>g.Key,g=>g.ToArray());
        DominatorInfo? dominance=null;var count=0;
        foreach(var allocation in graph.Instructions.Where(i=>i.OpCode==OpCode.Newobj).ToArray())
        {
            if(allocation.Operands is not [LocalVariable destination,LocalVariable metadata]
                || method.ParameterLocals.Contains(metadata) || method.ParameterLocals.Contains(destination)
                || !definitions.TryGetValue(metadata,out var reads) || reads.Length!=1
                || !definitions.TryGetValue(destination,out var allocations) || allocations.Length!=1
                || !ReferenceEquals(allocations[0],allocation))continue;
            var read=reads[0];
            if(MetadataResolver.RepeatedGotMetadataAddress(read,graph,definitions,method.AppContext.Binary.PointerSizeBytes,
                    readGot,ref dominance) is not { } address || resolveType(address) is not {IsValueType:false} type
                || type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                || type.HasAnyGenericParameters()
                || destination.Type!=null && !SameOrProvenBase(type,destination.Type))continue;
            var origins=graph.Blocks.Where(b=>b.Instructions.Contains(read)).ToArray();
            var targets=graph.Blocks.Where(b=>b.Instructions.Contains(allocation)).ToArray();
            if(origins.Length!=1 || targets.Length!=1)continue;
            if(ReferenceEquals(origins[0],targets[0]))
            {
                if(origins[0].Instructions.IndexOf(read)>=origins[0].Instructions.IndexOf(allocation))continue;
            }
            else
            {
                dominance??=new DominatorInfo(graph);
                if(!dominance.Dominates(origins[0],targets[0]))continue;
            }
            allocation.SetOperand(1,type);
            destination.Type=type;
            count++;
        }
        if(count>0)DeadCodeEliminator.Run(graph);
        return count;
    }

    private static bool SameOrProvenBase(TypeAnalysisContext actual,TypeAnalysisContext expected)
    {
        var visited=new System.Collections.Generic.HashSet<TypeAnalysisContext>();
        for(TypeAnalysisContext? type=actual;type!=null && visited.Add(type);type=type.BaseType)
            if(TrivialConstructorRecovery.SameType(type,expected))return true;
        return false;
    }
}
