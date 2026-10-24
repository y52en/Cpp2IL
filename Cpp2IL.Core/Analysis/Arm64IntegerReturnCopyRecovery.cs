using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Before SSA: an ordinary <=16-byte aggregate can return in X0/X1. A full
// adjacent copy must not interpret X1 as the caller's stale pre-call argument.
// Only complete copies with no other live low/high-register consumers qualify.
public static class Arm64IntegerReturnCopyRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes!=8 || method.ControlFlowGraph is not {} cfg)return 0;
        var changed=0;
        foreach(var block in cfg.Blocks.ToArray())
        foreach(var call in block.Instructions.ToArray())
        {
            if(call is not {OpCode:OpCode.Call,Operands:[Immediate address,Register result,..]}
                || result.Name!="X0" || !method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue,out var targets)
                || targets.Count!=1)continue;
            var target=targets[0];var type=target.ReturnType;
            if(target.IsVoid || !type.IsValueType || type.HasAnyGenericParameters()
                || TypeSizes.IsScalarValueType(type) || Arm64HfaLayout.Fields(type)!=null
                || method.AppContext.InstructionSet.CallingConventionResolver!.ReturnsViaHiddenBuffer(target))continue;
            var size=TypeSizes.UnboxedSize(type,8);var highWidth=size-8;
            if(highWidth is not (1 or 2 or 4 or 8))continue;
            var at=block.Instructions.IndexOf(call)+1;var consumer=block;
            if(at==block.Instructions.Count)
            {
                if(block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)continue;
                consumer=block.Successors[0];at=0;
            }
            if(at+1>=consumer.Instructions.Count)continue;
            var low=consumer.Instructions[at];var high=consumer.Instructions[at+1];
            if(low is not {OpCode:OpCode.Move,NativeWriteSize:8,
                    Operands:[MemoryOperand {Base:Register basis,Index:null,Scale:0} destination,Register lowValue]}
                || lowValue.Name!="X0" || basis.Name is "X0" or "X1" || destination.Addend>long.MaxValue-8
                || high is not {OpCode:OpCode.Move,Operands:[MemoryOperand {Base:Register highBase,Index:null,Scale:0} upper,Register highValue]}
                || highValue.Name!="X1" || high.NativeWriteSize!=highWidth
                || !basis.Equals(highBase) || upper.Addend!=destination.Addend+8
                || low.ImplicitDefinition!=null || high.ImplicitDefinition!=null
                || !UnobservedAfter(method,consumer,at+2))continue;
            low.NativeWriteSize=checked((int)size);
            high.OpCode=OpCode.Nop;high.SetOperands();high.NativeWriteSize=0;high.NativeZeroSize=0;
            changed++;
        }
        return changed;
    }

    private static bool UnobservedAfter(MethodAnalysisContext method,Block start,int index)
    {
        var pending=new Queue<(Block Block,int Index,int Live)>();pending.Enqueue((start,index,3));
        var seen=new HashSet<(Block,int,int)>();var budget=0;
        while(pending.TryDequeue(out var point))
        {
            if(!seen.Add(point))continue;
            var live=point.Live;
            for(var i=point.Index;i<point.Block.Instructions.Count;i++)
            {
                if(++budget>512)return false;
                var instruction=point.Block.Instructions[i];
                if(instruction.OpCode==OpCode.Return && method.IsVoid)break;
                foreach(var operand in instruction.Operands)
                    if(!(operand is Register && Equals(operand,instruction.Destination))
                        && ((live&1)!=0 && Uses(operand,"X0") || (live&2)!=0 && Uses(operand,"X1")))return false;
                if(instruction.Destination is Register written)
                {if(written.Name=="X0")live&=~1;if(written.Name=="X1")live&=~2;}
                // Unknown call ABI/clobbers cannot license skipping a use.
                if(instruction.ImplicitDefinition is {} implicitRegister
                    && ((live&1)!=0 && implicitRegister.Name=="X0" || (live&2)!=0 && implicitRegister.Name=="X1"))return false;
                if(live==0)break;
            }
            if(live!=0)foreach(var successor in point.Block.Successors)pending.Enqueue((successor,0,live));
        }
        return true;
    }
    private static bool Uses(IOperand operand,string name)=>operand switch
    {
        Register r=>r.Name==name,
        MemoryOperand m=>m.Base!=null && Uses(m.Base,name) || m.Index!=null && Uses(m.Index,name),
        AddressOf a=>Uses(a.Target,name),
        _=>false
    };
}
