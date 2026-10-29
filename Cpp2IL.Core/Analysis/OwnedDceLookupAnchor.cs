using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// A resolved dispatch makes its invoke-data phi dead before unrelated virtual
// calls finish binding. Only OUR observed DCE may authorize a retry without
// that phi. Every region, side-effect and escape proof is still rerun.
internal sealed class OwnedDceLookupAnchor
{
    private readonly ISILControlFlowGraph _graph;
    private readonly Instruction _dispatch;
    private readonly InterfaceDispatchRecovery.Match _match;
    private readonly IOperand[] _slowOperands;
    private readonly OpCode _slowOpcode;
    private readonly bool _slowVirtual;

    private OwnedDceLookupAnchor(ISILControlFlowGraph graph, Instruction dispatch,
        InterfaceDispatchRecovery.Match match)
    {
        _graph=graph;_dispatch=dispatch;_match=match;
        _slowOperands=match.SlowCall.Operands.ToArray();
        _slowOpcode=match.SlowCall.OpCode;_slowVirtual=match.SlowCall.NativeVirtualDispatch;
    }

    internal bool IsCurrent(ISILControlFlowGraph graph,Instruction dispatch,
        InterfaceDispatchRecovery.Match match)
    {
        if(!ReferenceEquals(graph,_graph) || !ReferenceEquals(dispatch,_dispatch)
            || !ReferenceEquals(match.InvokeDataPhi,_match.InvokeDataPhi)
            || !ReferenceEquals(match.Merge,_match.Merge)
            || !ReferenceEquals(match.SlowCall,_match.SlowCall)
            || !ReferenceEquals(match.Resolved,_match.Resolved)
            || !ReferenceEquals(match.KlassLocal,_match.KlassLocal)
            || !graph.Blocks.Contains(match.Merge)
            || !match.Merge.Instructions.Contains(match.InvokeDataPhi)
            || match.InvokeDataPhi.OpCode!=OpCode.Nop || match.InvokeDataPhi.Operands.Count!=0
            || !graph.Instructions.Contains(dispatch) || !graph.Instructions.Contains(match.SlowCall)
            || !dispatch.NativeVirtualDispatch || dispatch.OpCode is not (OpCode.Call or OpCode.CallVoid)
            || dispatch.Operands.Count==0 || !ReferenceEquals(dispatch.Operands[0],match.Resolved)
            || match.SlowCall.OpCode!=_slowOpcode || match.SlowCall.NativeVirtualDispatch!=_slowVirtual
            || !match.SlowCall.Operands.SequenceEqual(_slowOperands))return false;
        return true;
    }

    internal static List<OwnedDceLookupAnchor> Eliminate(ISILControlFlowGraph graph,
        IEnumerable<(Instruction Dispatch,InterfaceDispatchRecovery.Match Lookup)> lookups)
    {
        // Capture only live, metadata-bound phis immediately before this exact
        // invocation. A preexisting Nop or a foreign node never gets a receipt.
        var candidates=lookups.Where(p=>
                InterfaceDispatchRecovery.IsCurrentResolvedLookup(graph,p.Dispatch,p.Lookup.InvokeDataPhi,p.Lookup.Resolved)
                && graph.Blocks.Contains(p.Lookup.Merge)
                && p.Lookup.Merge.Instructions.Contains(p.Lookup.InvokeDataPhi)
                && graph.Instructions.Contains(p.Lookup.SlowCall)
                && p.Lookup.SlowCall.OpCode==OpCode.Call && !p.Lookup.SlowCall.NativeVirtualDispatch)
            .Select(p=>new OwnedDceLookupAnchor(graph,p.Dispatch,p.Lookup)).ToArray();
        DeadCodeEliminator.Run(graph);
        return candidates.Where(p=>p.IsCurrent(graph,p._dispatch,p._match)).ToList();
    }
}
