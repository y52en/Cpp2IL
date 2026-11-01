using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// Handles a metadata-init prefix whose final business condition was duplicated
// into both successors of the flag guard. Prove matching byte flag addresses,
// resolved init calls, equivalent business exits, and no escaping definitions.
// No arbitrary call/store, live value, or unknown condition can be discarded.
public static class MetadataInitForkRecovery
{
    public static int Run(ISILControlFlowGraph graph)
    {
        var changed=0;
        foreach(var guard in graph.Blocks.ToArray())
        {
            var definitions=graph.Blocks.SelectMany(b=>b.Instructions)
                .Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
                .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
            if(guard.Successors.Count!=2 || guard.Instructions.LastOrDefault() is not
                {OpCode:OpCode.ConditionalJump,Operands:[_,var condition]})continue;
            if(!FlagAddress(condition,definitions,out var address))continue;
            var a=guard.Successors[0];var b=guard.Successors[1];
            if(TryRemove(graph,guard,a,b,address,definitions)
                || TryRemove(graph,guard,b,a,address,definitions))changed++;
        }
        if(changed>0)DeadCodeEliminator.Run(graph);
        return changed;
    }

    private static bool TryRemove(ISILControlFlowGraph graph,Block guard,Block init,Block plain,long address,
        Dictionary<LocalVariable,Instruction> definitions)
    {
        if(init==plain || init==guard || plain==guard || init==graph.EntryBlock || init==graph.ExitBlock
            || plain==graph.EntryBlock || plain==graph.ExitBlock
            || init.Predecessors.Count!=1 || init.Predecessors[0]!=guard
            || plain.Predecessors.Count!=1 || plain.Predecessors[0]!=guard
            || init.Successors.Count!=2 || plain.Successors.Count!=2
            || init.Successors.Distinct().Count()!=2
            || !init.Successors.ToHashSet().SetEquals(plain.Successors)
            || init.Successors.Any(b=>b==guard || b==init || b==plain))return false;
        if(!BusinessBranch(init,definitions,out var ic,out var it,out var iff)
            || !BusinessBranch(plain,definitions,out var pc,out var pt,out var pf)
            || !ic.Equals(pc) || it!=pt || iff!=pf)return false;
        // The bypass block must contain only the business predicate, with no
        // memory/call effects that could be skipped or duplicated by the cut.
        if(plain.Instructions.Any(i=>i.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.Not
            or OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.ConditionalJump)
            || i.OpCode==OpCode.Move && i.Operands is not [LocalVariable,LocalVariable]))return false;
        var calls=0;var stores=0;
        foreach(var instruction in init.Instructions)
        {
            if(instruction.OpCode==OpCode.Nop || instruction.OpCode==OpCode.ConditionalJump)continue;
            if(instruction.OpCode is OpCode.Call or OpCode.CallVoid)
            {
                if(instruction.Operands[0] is not StringLiteral {Value:
                    "il2cpp_codegen_initialize_method" or "il2cpp_codegen_initialize_runtime_metadata"})return false;
                calls++;continue;
            }
            if(instruction is {OpCode:OpCode.Move,Operands:[MemoryOperand memory,var value]})
            {
                if(instruction.NativeWriteSize!=1 || !Absolute(memory,definitions,out var stored)
                    || stored!=address || !Constant(value,definitions,out var one) || one!=1)return false;
                stores++;continue;
            }
            if(instruction.Destination is not LocalVariable || instruction.OpCode is not
                (OpCode.Move or OpCode.Or or OpCode.And or OpCode.Not or OpCode.CheckEqual or OpCode.CheckNotEqual))return false;
            // Only raw native reads and register/immediate operations qualify.
            if(instruction.Operands.Skip(1).Any(o=>o is not (LocalVariable or Immediate or MemoryOperand)))return false;
        }
        if(calls==0 || stores!=1)return false;
        var produced=init.Instructions.Select(i=>i.Destination).OfType<LocalVariable>().ToHashSet();
        if(graph.Blocks.Where(b=>b!=init).SelectMany(b=>b.Instructions)
            .Any(i=>InterfaceDispatchRecovery.UsedLocals(i).Any(produced.Contains)))return false;
        var plainProduced=plain.Instructions.Select(i=>i.Destination).OfType<LocalVariable>().ToHashSet();
        if(graph.Blocks.Where(b=>b!=plain).SelectMany(b=>b.Instructions)
            .Any(i=>InterfaceDispatchRecovery.UsedLocals(i).Any(plainProduced.Contains)))return false;
        // Both business arms reach the same successor with identical values.
        // Remove only the unreachable init predecessor's phi inputs.
        foreach(var exit in init.Successors)
        {
            var ii=exit.Predecessors.IndexOf(init);var pi=exit.Predecessors.IndexOf(plain);
            if(ii<0 || pi<0 || exit.Predecessors.Count(b=>b==init)!=1
                || exit.Predecessors.Count(b=>b==plain)!=1)return false;
            foreach(var phi in exit.Instructions.Where(i=>i.OpCode==OpCode.Phi))
                if(phi.Operands.Count!=exit.Predecessors.Count+1
                    || !Equals(phi.Operands[ii+1],phi.Operands[pi+1]))return false;
        }
        foreach(var exit in init.Successors.ToArray())
        {
            var index=exit.Predecessors.IndexOf(init);
            foreach(var phi in exit.Instructions.Where(i=>i.OpCode==OpCode.Phi))phi.RemoveOperandAt(index+1);
            exit.Predecessors.RemoveAt(index);
        }
        guard.Instructions[^1].OpCode=OpCode.Jump;guard.Instructions[^1].SetOperands(plain);
        guard.Successors.Clear();guard.Successors.Add(plain);guard.CalculateBlockType();
        init.Predecessors.Clear();init.Successors.Clear();graph.Blocks.Remove(init);
        return true;
    }

    private static bool BusinessBranch(Block block,Dictionary<LocalVariable,Instruction> defs,
        out (IOperand,IOperand) condition,out Block yes,out Block no)
    {
        condition=default;yes=null!;no=null!;
        if(block.Instructions.LastOrDefault() is not {OpCode:OpCode.ConditionalJump,Operands:[Block target,var operand]}
            || !block.Successors.Contains(target))return false;
        var invert=false;var visited=new HashSet<LocalVariable>();
        while(operand is LocalVariable local && visited.Add(local) && defs.TryGetValue(local,out var d))
        {
            if(d is {OpCode:OpCode.Move,Operands:[_,var copy]}){operand=copy;continue;}
            if(d is {OpCode:OpCode.Not,Operands:[_,var source]}){invert=!invert;operand=source;continue;}
            if(d.OpCode is not(OpCode.CheckEqual or OpCode.CheckNotEqual) || d.Operands.Count!=3)return false;
            invert^=d.OpCode==OpCode.CheckNotEqual;
            condition=(d.Operands[1],d.Operands[2]);yes=target;no=block.Successors.Single(b=>b!=target);
            if(invert)(yes,no)=(no,yes);
            return true;
        }
        return false;
    }

    private static bool FlagAddress(IOperand operand,Dictionary<LocalVariable,Instruction> defs,out long address)
    {
        address=0;
        if(operand is not LocalVariable condition || !defs.TryGetValue(condition,out var compare)
            || compare is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,Operands:[_,LocalVariable masked,Immediate {Value:0}]}
            || !defs.TryGetValue(masked,out var and) || and is not {OpCode:OpCode.And,Operands:[_,LocalVariable flag,Immediate {Value:1}]}
            || !defs.TryGetValue(flag,out var load) || load is not {OpCode:OpCode.Move,NativeReadSize:1,Operands:[_,MemoryOperand memory]})return false;
        return Absolute(memory,defs,out address);
    }

    private static bool Absolute(MemoryOperand memory,Dictionary<LocalVariable,Instruction> defs,out long address)
    {
        address=memory.Addend;if(memory.Index!=null || memory.Scale!=0)return false;
        if(memory.Base==null)return true;
        if(!Constant(memory.Base,defs,out var value))return false;
        try{address=checked(value+address);return true;}catch(System.OverflowException){return false;}
    }

    private static bool Constant(IOperand operand,Dictionary<LocalVariable,Instruction> defs,out long value,int depth=0)
    {
        value=0;if(depth>32)return false;
        if(operand is Immediate immediate){value=immediate.Value;return true;}
        if(operand is not LocalVariable local || !defs.TryGetValue(local,out var d))return false;
        if(d is {OpCode:OpCode.Move,Operands:[_,var copy]})return Constant(copy,defs,out value,depth+1);
        if(d is {OpCode:OpCode.Or,Operands:[_,var left,var right]}
            && Constant(left,defs,out var a,depth+1) && Constant(right,defs,out var b,depth+1))
        {value=a|b;return true;}
        return false;
    }
}
