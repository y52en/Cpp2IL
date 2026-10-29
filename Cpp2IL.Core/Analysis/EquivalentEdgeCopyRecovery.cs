using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// SSA destruction can split the identical null-result assignment into one
// block per failure edge. Share only exactly identical, effect-free copies.
// No memory access/call/arithmetic/phi or inferred type conversion is removed.
public static class EquivalentEdgeCopyRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var groups=new Dictionary<Block,List<(Block Block,Instruction[] Copies)>>();
        foreach(var block in graph.Blocks)
        {
            if(ReferenceEquals(block,graph.EntryBlock)||ReferenceEquals(block,graph.ExitBlock)
                ||block.Successors.Count!=1||block.Predecessors.Count==0)continue;
            var next=block.Successors[0];
            if(ReferenceEquals(next,block)||next.Instructions.Any(i=>i.OpCode==OpCode.Phi))continue;
            var body=block.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
            if(body.LastOrDefault() is {OpCode:OpCode.Jump,Operands:[Block target]})
            {
                if(!ReferenceEquals(target,next))continue;
                body=body[..^1];
            }
            if(body.Length is <1 or >8 || body.Any(i=>i is not
                {OpCode:OpCode.Move,Operands:[LocalVariable,var source],ImplicitDefinition:null,
                    NativeReadSize:0,NativeWriteSize:0,NativeArithmeticSize:0,NativeIntegerSourceView:false,
                    NativeFloatingPointSize:0,NativeZeroSize:0}
                ||source is not (LocalVariable or Immediate)))continue;
            if(!groups.TryGetValue(next,out var choices))groups[next]=choices=[];
            choices.Add((block,body));
        }
        var changes=0;
        foreach(var choices in groups.Values)
        {
            var canonical=new List<(Block Block,Instruction[] Copies)>();
            foreach(var item in choices)
            {
                var found=canonical.FirstOrDefault(other=>Same(other.Copies,item.Copies));
                if(found.Block==null){canonical.Add(item);continue;}
                var block=item.Block;var target=found.Block;
                var incoming=block.Predecessors.ToArray();
                // Do not create duplicate successor edges or synthesize a
                // missing branch target. Refuse the entire block atomically.
                if(incoming.Any(p=>p.Successors.Contains(target)||p.Instructions.Any(i=>i.OpCode==OpCode.Phi)
                    ||p.Instructions.LastOrDefault() is not {OpCode:OpCode.Jump or OpCode.ConditionalJump}))continue;
                foreach(var predecessor in incoming)
                {
                    var at=predecessor.Successors.IndexOf(block);
                    predecessor.Successors[at]=target;target.Predecessors.Add(predecessor);
                    foreach(var instruction in predecessor.Instructions)
                        for(var n=0;n<instruction.Operands.Count;n++)
                            if(ReferenceEquals(instruction.Operands[n],block))instruction.SetOperand(n,target);
                    block.Predecessors.Remove(predecessor);
                }
                graph.RemoveEdge(block,block.Successors[0]);graph.Blocks.Remove(block);changes++;
            }
        }
        return changes;
    }
    static bool Same(Instruction[] a,Instruction[] b)=>a.Length==b.Length&&a.Zip(b,(x,y)=>
        ReferenceEquals(x.Operands[0],y.Operands[0])&&x.NativeRegisterCopySize==y.NativeRegisterCopySize
        &&(ReferenceEquals(x.Operands[1],y.Operands[1])||x.Operands[1]is Immediate u&&y.Operands[1]is Immediate v&&u.Value==v.Value)).All(x=>x);
}
