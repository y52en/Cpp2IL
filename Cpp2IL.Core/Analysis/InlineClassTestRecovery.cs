using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Analysis;

// Same inspected Unity2018 ARM64 class hierarchy kernel as checked casts,
// but BOTH application outcomes remain intact. An isinst is not castclass.
public static class InlineClassTestRecovery
{
    public static int Run(MethodAnalysisContext method)
        => method.AppContext.InstructionSet is NewArmV8InstructionSet
            && method.AppContext.UnityVersion.Major==2018 && method.AppContext.UnityVersion.Minor==4
            && method.AppContext.Binary.PointerSizeBytes==8 ? Recover(method):0;

    public static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not { } cfg)return 0;
        if(!cfg.Instructions.Any(i=>i is {OpCode:OpCode.Move,NativeReadSize:1,
            Operands:[_,MemoryOperand {Addend:0x120}]}))return 0;
        var count=0;
        foreach(var depth in cfg.Blocks.ToArray())
        {
            if(!cfg.Blocks.Contains(depth) || depth.Successors.Count!=2
                || depth.Instructions.LastOrDefault()?.OpCode!=OpCode.ConditionalJump)continue;
            var defs=cfg.Instructions.Where(i=>i.Destination is LocalVariable)
                .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()==1)
                .ToDictionary(g=>g.Key,g=>g.Single());
            var match=InlineClassCastRecovery.TryMatch(depth,defs);
            if(match?.Object is not LocalVariable {Type.IsValueType:false} source
                || source.Type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                || !InlineClassCastRecovery.HasNullBypass(match,defs))continue;
            var insertion=CheckInsertionBlock(method,match,source);
            if(insertion==null)continue;
            var kernel=new HashSet<Block>{depth,match.Ancestor};
            var instructions=kernel.SelectMany(b=>b.Instructions).ToArray();
            if(instructions.Any(i=>ReferenceEquals(i.Destination,source)) || !PureKernel(match)
                || match.Success.Instructions.Any(i=>i.OpCode==OpCode.Phi)
                || match.Failure.Instructions.Any(i=>i.OpCode==OpCode.Phi))continue;
            var defined=instructions.Select(i=>i.Destination).OfType<LocalVariable>().ToArray();
            if(cfg.Blocks.Where(b=>!kernel.Contains(b)).SelectMany(b=>b.Instructions).SelectMany(i=>i.Operands)
                .Any(o=>defined.Any(l=>Contains(o,l))))continue;
            var bypass=new HashSet<Block>();var pending=new Queue<Block>();pending.Enqueue(cfg.EntryBlock);
            while(pending.TryDequeue(out var block))
            {
                if(ReferenceEquals(block,match.Success) || !bypass.Add(block))continue;
                foreach(var next in block.Successors)pending.Enqueue(next);
            }
            var result=new LocalVariable("isinst_"+depth.ID,new(null,"isinst_"+depth.ID),match.Target);
            var flag=new LocalVariable("isinst_null_"+depth.ID,new(null,"isinst_null_"+depth.ID),method.AppContext.SystemTypes.SystemBooleanType);
            method.Locals.Add(result);method.Locals.Add(flag);
            var index=depth.Instructions.Last().Index;
            var managedCheck=new Instruction(index,OpCode.IsInst,result,match.Target,source);
            depth.Instructions=[new(index,OpCode.CheckEqual,flag,result,new Immediate(0)),
                new(index,OpCode.ConditionalJump,match.Failure,flag)];
            if(ReferenceEquals(insertion,depth))depth.Instructions.Insert(0,managedCheck);
            else insertion.Instructions.Insert(insertion.Instructions.Count-1,managedCheck);
            cfg.RemoveEdge(depth,match.Ancestor);cfg.RemoveEdge(match.Ancestor,match.Failure);
            cfg.RemoveEdge(match.Ancestor,match.Success);
            depth.Successors.Add(match.Success);match.Success.Predecessors.Add(depth);
            cfg.RemoveUnreachableBlocks();
            foreach(var block in cfg.Blocks.Where(b=>!bypass.Contains(b)))
                foreach(var instruction in block.Instructions)
                    for(var n=0;n<instruction.Operands.Count;n++)
                        if(!ReferenceEquals(instruction.Operands[n],instruction.Destination))
                            instruction.SetOperand(n,InlineClassCastRecovery.Replace(instruction.Operands[n],source,result));
            depth.CalculateBlockType();count++;
        }
        if(count>0)DeadCodeEliminator.Run(cfg);
        return count;
    }

    // A check result must be defined on EVERY incoming success path. A direct
    // null bypass may share success with the ancestor check: evaluate isinst/
    // castclass before that null branch (both preserve null), not just in the
    // non-null depth block. No arbitrary extra predecessor/phi is accepted.
    internal static Block? CheckInsertionBlock(MethodAnalysisContext method,InlineClassCastRecovery.Match match,LocalVariable source)
    {
        if(match.Success.Predecessors.Count==1)
            return StableSource(method,source,match.Depth)?match.Depth:null;
        if(match.Depth.Predecessors.Count!=1 || match.Success.Predecessors.Count!=2)return null;
        var guard=match.Depth.Predecessors[0];
        if(!match.Success.Predecessors.Contains(guard) || !match.Success.Predecessors.Contains(match.Ancestor)
            || !guard.Successors.Contains(match.Success) || !PureKernel(match)
            || !StableSource(method,source,guard))return null;
        return guard;
    }

    internal static bool StableSource(MethodAnalysisContext method,LocalVariable source,Block consumer)
    {
        if(source.Type is not {IsValueType:false}
            || source.Type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
            || method.ControlFlowGraph is not { } cfg)return false;
        var writes=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,source)).ToArray();
        if(method.ParameterLocals.Contains(source))return writes.Length==0;
        if(writes.Length!=1)return false;
        var blocks=cfg.Blocks.Where(b=>b.Instructions.Contains(writes[0])).ToArray();
        if(blocks.Length!=1)return false;
        if(ReferenceEquals(blocks[0],consumer))
            return consumer.Instructions.IndexOf(writes[0])<consumer.Instructions.Count-1;
        return new DominatorInfo(cfg).Dominates(blocks[0],consumer);
    }

    internal static bool PureKernel(InlineClassCastRecovery.Match match)
    {
        var instructions=match.Depth.Instructions.Concat(match.Ancestor.Instructions).ToArray();
        if(instructions.Any(i=>i.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.Add
                or OpCode.ShiftLeft or OpCode.CheckLess or OpCode.CheckGreaterOrEqual
                or OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.Not or OpCode.ConditionalJump)
                || i.Destination is MemoryOperand or FieldReference)
            || instructions.Any(i=>i.Operands.Any(o=>o is not
                (LocalVariable or Immediate or TypeAnalysisContext or MemoryOperand or Block)
                || o is MemoryOperand && i.OpCode!=OpCode.Move)))return false;
        var loads=instructions.Where(i=>i.OpCode==OpCode.Move && i.Operands.Count==2 && i.Operands[1] is MemoryOperand).ToArray();
        return loads.Length==5 && loads.All(i=>i.Operands[1] is MemoryOperand {Index:null,Scale:0})
            && loads.Count(i=>((MemoryOperand)i.Operands[1]).Addend==0 && i.NativeReadSize==8)==1
            && loads.Count(i=>((MemoryOperand)i.Operands[1]).Addend==0x120 && i.NativeReadSize==1)==2
            && loads.Count(i=>((MemoryOperand)i.Operands[1]).Addend==0xC8 && i.NativeReadSize==8)==1
            && loads.Count(i=>((MemoryOperand)i.Operands[1]).Addend==-8 && i.NativeReadSize==8)==1;
    }

    private static bool Contains(IOperand operand,LocalVariable local)=>operand switch
    {
        LocalVariable candidate=>ReferenceEquals(candidate,local),
        MemoryOperand m=>(m.Base!=null && Contains(m.Base,local)) || (m.Index!=null && Contains(m.Index,local)),
        FieldReference f=>ReferenceEquals(f.Local,local) || f.Parent!=null && Contains(f.Parent,local),
        AddressOf a=>Contains(a.Target,local),ArrayAccess a=>ReferenceEquals(a.Array,local) || Contains(a.Index,local),
        ArrayLength a=>ReferenceEquals(a.Array,local),_=>false
    };
}
