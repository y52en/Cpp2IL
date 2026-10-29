using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Graphs;

namespace Cpp2IL.Core.Analysis;

// This preserves all caller stores and branches. It does not guess constructor
// arguments: the selected complete native template with zero scalar inputs is
// proven to be an identity operation on this newly allocated zero-filled object.
public static class ZeroStateConstructorRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.AppContext.UnityVersion.Major!=2018 || method.AppContext.UnityVersion.Minor!=4
            || method.AppContext.Binary.PointerSizeBytes!=8
            || method.AppContext.InstructionSet is not NewArmV8InstructionSet)return 0;
        return Recover(method);
    }

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var recovered=0;
        foreach(var allocation in graph.Instructions.Where(i=>i.OpCode==OpCode.Newobj).ToArray())
        {
            if(allocation.Operands is not [LocalVariable obj,TypeAnalysisContext owner]
                || graph.Instructions.Count(i=>ReferenceEquals(i.Destination,obj))!=1)continue;
            var templates=owner.GetExtraData<InlinedConstructorRecovery.Template[]>(InlinedConstructorRecovery.CacheKey)??[];
            var matches=templates.Select(t=>(Template:t,Arguments:InlinedConstructorRecovery.ZeroStateArguments(t,owner)))
                .Where(t=>t.Arguments!=null).ToArray();
            // Different callable constructors remain ambiguous even when both
            // zero-state templates look harmless. Never choose by name/arity.
            if(matches.Length!=1)continue;
            var block=graph.Blocks.Single(b=>b.Instructions.Contains(allocation));
            // Native call barriers split a straight-line initialization into
            // separate blocks. Follow only unique-successor/unique-predecessor
            // continuations; merges, branches, cycles and effects still stop.
            var scan=block.Instructions.Skip(block.Instructions.IndexOf(allocation)+1).ToList();
            var seen=new HashSet<Block>{block};var current=block;
            while(current.Successors.Count==1 && current.Successors[0].Predecessors.Count==1
                && seen.Count<8 && seen.Add(current.Successors[0]))
            {current=current.Successors[0];scan.AddRange(current.Instructions);}
            var aliases=new HashSet<LocalVariable>{obj};
            foreach(var instruction in scan.Take(12))
            {
                if(instruction.OpCode==OpCode.Nop)continue;
                if(instruction.OpCode==OpCode.Jump)continue;
                if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]}
                    && aliases.Contains(source)
                    && graph.Instructions.Count(i=>ReferenceEquals(i.Destination,alias))==1)
                {aliases.Add(alias);continue;}
                if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                    Operands:[MethodAnalysisContext parent,LocalVariable receiver]}
                    && aliases.Contains(receiver) && parent.Name==".ctor" && !parent.IsStatic && parent.IsVoid
                    && parent.Parameters.Count==0
                    && ReferenceEquals(parent,matches[0].Template.BaseConstructor)
                    && parent.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey)
                        is {IsNoOp:true})
                {
                    instruction.SetOperands(new List<IOperand>{matches[0].Template.Constructor,receiver}
                        .Concat(matches[0].Arguments!).ToList());
                    recovered++;
                }
                break;
            }
        }
        return recovered;
    }
}
