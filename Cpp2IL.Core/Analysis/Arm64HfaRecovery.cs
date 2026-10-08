using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Before SSA: preserve each native SIMD lane while exposing one managed struct.
public static class Arm64HfaRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is not NewArmV8InstructionSet) return false;
        var graph=method.ControlFlowGraph!;
        var resolver=method.AppContext.InstructionSet.CallingConventionResolver!;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
        Instruction Move(IOperand to,IOperand from)=>new(serial++,OpCode.Move,to,from);
        var changed=false;
        var entry=new List<Instruction>();
        var incoming=resolver.ResolveForManaged(method);
        foreach(var item in Parameters(method,incoming))
            for(var lane=0;lane<item.Fields.Length;lane++)
                entry.Add(Move(new Register(null,"V"+(item.FirstLane+lane)),new MemoryOperand(item.Storage,addend:item.Fields[lane].Offset)));
        if(entry.Count>0){graph.EntryBlock.Instructions.InsertRange(0,entry);changed=true;}
        foreach(var block in graph.Blocks.ToArray())
        for(var index=0;index<block.Instructions.Count;index++)
        {
            var instruction=block.Instructions[index];
            if(instruction.IsCall && instruction.Operands[0] is Immediate address
                && method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue,out var targets) && targets.Count==1)
            {
                var target=targets[0];var arguments=resolver.ResolveForManaged(target);
                var prefix=new List<Instruction>();
                foreach(var item in Parameters(target,arguments))
                {
                    prefix.Add(Move(item.Storage,new DefaultStructValue(item.Type)));
                    for(var lane=0;lane<item.Fields.Length;lane++)
                        prefix.Add(Move(new MemoryOperand(item.Storage,addend:item.Fields[lane].Offset),new Register(null,"V"+(item.FirstLane+lane))));
                }
                if(prefix.Count>0)
                {
                    block.Instructions.InsertRange(index,prefix);index+=prefix.Count;
                    var first=instruction.OpCode==OpCode.CallVoid?1:2;
                    var operands=instruction.Operands.Take(first).Concat(arguments).ToList();
                    instruction.SetOperands(operands);changed=true;
                }
                if(instruction.OpCode==OpCode.Call && Arm64HfaLayout.Fields(target.ReturnType) is { } fields)
                {
                    var result=new Register(null,"hfa_result_"+serial++);
                    instruction.Destination=result;
                    var suffix=fields.Select((field,lane)=>Move(new Register(null,"V"+lane),new MemoryOperand(result,addend:field.Offset))).ToList();
                    // Call-block consumers require the actual call to remain
                    // last. Project lanes on a dedicated successor edge, not
                    // after the call inside its block.
                    var projection=new Block {ID=graph.Blocks.Max(b=>b.ID)+1,BlockType=BlockType.Fall,Instructions=suffix};
                    projection.Predecessors.Add(block);
                    projection.Successors=block.Successors;
                    foreach(var successor in projection.Successors)
                        for(var p=0;p<successor.Predecessors.Count;p++)
                            if(successor.Predecessors[p]==block) successor.Predecessors[p]=projection;
                    block.Successors=[projection];graph.Blocks.Add(projection);changed=true;
                }
            }
            else if(instruction.OpCode==OpCode.Return && Arm64HfaLayout.Fields(method.ReturnType) is { } fields)
            {
                var result=new Register(null,"hfa_return_"+serial++);
                var prefix=new List<Instruction>{Move(result,new DefaultStructValue(method.ReturnType))};
                prefix.AddRange(fields.Select((field,lane)=>Move(new MemoryOperand(result,addend:field.Offset),new Register(null,"V"+lane))));
                block.Instructions.InsertRange(index,prefix);index+=prefix.Count;
                instruction.SetOperands(result);changed=true;
            }
        }
        return changed;
    }

    private static IEnumerable<(Register Storage,TypeAnalysisContext Type,FieldAnalysisContext[] Fields,int FirstLane)> Parameters(MethodAnalysisContext method,IOperand[] operands)
    {
        var floating=0;
        for(var p=0;p<method.Parameters.Count;p++)
        {
            var type=method.Parameters[p].ParameterType;
            if(Arm64HfaLayout.Fields(type) is { } fields)
            {
                var ordinal=p+(method.IsStatic?0:1);
                if(floating+fields.Length<=8 && operands[ordinal] is Register register)
                {
                    yield return (register,type,fields,floating);
                    floating+=fields.Length;
                }
                else floating=8;
            }
            else if(BaseCallingConventionResolver.IsFloatingPoint(type)) floating++;
        }
    }
}
