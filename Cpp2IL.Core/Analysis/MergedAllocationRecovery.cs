using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// After SSA removal a native tail merge can select distinct TypeInfos on its
// incoming edges, then allocate and call one inlined ancestor constructor.
// Specialize ONLY that complete allocation/constructor block per proven edge.
// No tests on type names, arbitrary common-base allocation, or moved effects.
public static class MergedAllocationRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} cfg)return 0;
        var count=0;
        foreach(var block in cfg.Blocks.ToArray())
            if(Recover(method,block))count++;
        return count;
    }

    internal static bool Recover(MethodAnalysisContext method,Block block)
    {
        if(method.ControlFlowGraph is not {} cfg || block==cfg.EntryBlock || block==cfg.ExitBlock
            || block.Predecessors.Count is <2 or >8 || block.Successors.Count!=1
            || block.Successors[0]==block || block.Predecessors.Distinct().Count()!=block.Predecessors.Count
            || cfg.Instructions.Any(i=>i.OpCode==OpCode.Phi))return false;
        var body=block.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(body.Length<2 || body[0] is not {OpCode:OpCode.Newobj,Operands:[LocalVariable obj,LocalVariable metadata]}
            || method.ParameterLocals.Contains(obj) || method.ParameterLocals.Contains(metadata)
            || ReferenceEquals(obj,metadata)
            || body[1] is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,ImplicitDefinition:null,
                Operands:[MethodAnalysisContext {Name:".ctor",IsStatic:false,IsVirtual:false,IsVoid:true} target,LocalVariable receiver,..]}
            || !ReferenceEquals(receiver,obj) || body[1].Operands.Count!=target.Parameters.Count+2)return false;
        var aliases=new HashSet<LocalVariable>{obj};
        foreach(var suffix in body.Skip(2))
        {
            if(suffix==body[^1] && suffix is {OpCode:OpCode.Jump,Operands:[Block destination]}
                && ReferenceEquals(destination,block.Successors[0]))continue;
            if(suffix is not {OpCode:OpCode.Move,ImplicitDefinition:null,Operands:[LocalVariable local,LocalVariable value]}
                || !aliases.Contains(value) || !aliases.Add(local) || ReferenceEquals(local,metadata))return false;
        }
        // A loop returning to this initialization could alter the coalesced
        // metadata/arguments. Restrict to a genuinely acyclic shared suffix.
        var pending=new Stack<Block>(block.Successors);var visited=new HashSet<Block>();
        while(pending.TryPop(out var next))
        {
            if(next==block || block.Predecessors.Contains(next))return false;
            if(!visited.Add(next))continue;
            if(visited.Count>512)return false;
            foreach(var successor in next.Successors)pending.Push(successor);
        }
        var plans=new List<(Block Before,TypeAnalysisContext Type,MethodAnalysisContext Constructor)>();
        foreach(var before in block.Predecessors)
        {
            if(before==cfg.EntryBlock || before.Successors.Count!=1 || before.Successors[0]!=block)return false;
            var definitions=before.Instructions.Where(i=>ReferenceEquals(i.Destination,metadata)).ToArray();
            if(definitions.Length!=1 || definitions[0] is not
                {OpCode:OpCode.Move,ImplicitDefinition:null,Operands:[_,TypeAnalysisContext type]}
                || type.IsValueType || type is RuntimeClassTypeAnalysisContext or PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                || type.HasAnyGenericParameters())return false;
            var at=before.Instructions.IndexOf(definitions[0]);
            if(before.Instructions.Skip(at+1).Any(i=>i.ImplicitDefinition!=null))return false;
            // Only block-target jumps are supported; instruction targets would
            // leave a dangling cross-edge reference after specialization.
            if(before.Instructions.Any(i=>i.Operands.Any(o=>o is Instruction)))return false;
            var matches=type.GetExtraData<ForwardedConstructorRecovery.Template[]>(ForwardedConstructorRecovery.CacheKey)?
                .Where(t=>ReferenceEquals(t.Constructor.DeclaringType,type) && ReferenceEquals(t.Base,target)
                    && t.Constructor.Parameters.Count==target.Parameters.Count).ToArray();
            if(matches is not {Length:1})return false;
            for(var n=0;n<target.Parameters.Count;n++)
                if(!TrivialConstructorRecovery.SameType(matches[0].Constructor.Parameters[n].ParameterType,target.Parameters[n].ParameterType))return false;
            DominatorInfo? dominance=null;
            if(body[1].Operands.Skip(2).Any(value=>!InlinedConstructorRecovery.AvailableBeforeAllocation(
                    value,method,cfg.Instructions,cfg.Instructions.IndexOf(body[0]),block,ref dominance,aliases)))return false;
            plans.Add((before,type,matches[0].Constructor));
        }
        if(plans.Select(p=>p.Type).Distinct().Count()<2)return false;
        // Commit only after ALL edges and constructors pass. Cloning preserves
        // instruction metadata and operands; each path still allocates once.
        var after=block.Successors[0];var nextId=cfg.Blocks.Max(b=>b.ID)+1;
        foreach(var plan in plans)
        {
            var copy=new Block{ID=nextId++,Predecessors=[plan.Before],Successors=[after]};
            foreach(var instruction in block.Instructions)
                copy.Instructions.Add(new(instruction.Index,instruction.OpCode,instruction.Operands.ToList())
                {
                    ImplicitDefinition=instruction.ImplicitDefinition,NativeWriteSize=instruction.NativeWriteSize,
                    NativeReadSize=instruction.NativeReadSize,NativeArithmeticSize=instruction.NativeArithmeticSize,
                    NativeRegisterCopySize=instruction.NativeRegisterCopySize,NativeFloatingPointSize=instruction.NativeFloatingPointSize,
                    UnsignedComparison=instruction.UnsignedComparison,NativeZeroSize=instruction.NativeZeroSize,
                    NativeVirtualDispatch=instruction.NativeVirtualDispatch,NativeDirectCallTarget=instruction.NativeDirectCallTarget
                });
            copy.Instructions[block.Instructions.IndexOf(body[0])].SetOperand(1,plan.Type);
            copy.Instructions[block.Instructions.IndexOf(body[1])].SetOperand(0,plan.Constructor);
            foreach(var instruction in plan.Before.Instructions)
                for(var n=0;n<instruction.Operands.Count;n++)
                    if(ReferenceEquals(instruction.Operands[n],block))instruction.SetOperand(n,copy);
            plan.Before.Successors[0]=copy;after.Predecessors.Add(copy);
            copy.CalculateBlockType();cfg.Blocks.Add(copy);
        }
        after.Predecessors.Remove(block);block.Predecessors.Clear();block.Successors.Clear();cfg.Blocks.Remove(block);
        method.DominatorInfo=null;
        return true;
    }
}
