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
        changed |= RecoverIncomingStackHfas(method, incoming);
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

    // An HFA that does not fit entirely in V0-V7 is passed wholly on the stack.
    // StackAnalyzer names each scalar load independently; do not seed stack_0
    // itself as both a whole Vector3 parameter and its first Single lane.
    internal static bool RecoverIncomingStackHfas(MethodAnalysisContext method, IOperand[] incoming)
    {
        var changed=false;
        var graph=method.ControlFlowGraph!;
        for(var p=0;p<method.Parameters.Count;p++)
        {
            var ordinal=p+(method.IsStatic?0:1);
            var type=method.Parameters[p].ParameterType;
            if(Arm64HfaLayout.Fields(type) is not { } fields
                || incoming[ordinal] is not StackOffset offset
                || method.ParameterOperands.Count<=ordinal
                || method.ParameterOperands[ordinal] is not Register parameter
                || parameter.Name!="stack_"+offset.Offset.ToString("X")) continue;
            var size=TypeSizes.UnboxedSize(type,8);
            var loads=new List<(Instruction Load,FieldAnalysisContext Field)>();
            var valid=true;
            foreach(var instruction in graph.Instructions)
            foreach(var operand in instruction.Operands)
            foreach(var register in StorageRegisters(operand))
            {
                if(!register.Name.StartsWith("stack_",System.StringComparison.Ordinal)
                    || !int.TryParse(register.Name.Substring(6),System.Globalization.NumberStyles.AllowHexSpecifier,
                        System.Globalization.CultureInfo.InvariantCulture,out var slot)
                    || slot<offset.Offset || slot>=offset.Offset+size) continue;
                var field=fields.SingleOrDefault(f=>f.Offset==slot-offset.Offset);
                // Only exact native scalar reads are proven. Writes, addresses,
                // ABI call operands, partial/unknown widths and other uses veto
                // this parameter rather than inventing its contents.
                if(operand is not Register || instruction.OpCode!=OpCode.Move
                    || instruction.Operands.Count!=2 || !ReferenceEquals(operand,instruction.Operands[1])
                    || instruction.Destination is not Register || field==null
                    || instruction.NativeReadSize<=0
                    || instruction.NativeReadSize!=TypeSizes.UnboxedSize(field.FieldType,8))
                { valid=false; break; }
                loads.Add((instruction,field));
            }
            if(!valid || loads.Count==0) continue;
            var storage=new Register(null,"hfa_stack_arg_"+p);
            method.ParameterOperands[ordinal]=storage;
            foreach(var (load,field) in loads)
                load.SetOperand(1,new MemoryOperand(storage,addend:field.Offset));
            changed=true;
        }
        return changed;
    }

    private static IEnumerable<Register> StorageRegisters(IOperand operand)
    {
        if(operand is Register register) yield return register;
        else if(operand is AddressOf address)
            foreach(var nested in StorageRegisters(address.Target)) yield return nested;
        else if(operand is MemoryOperand memory)
        {
            if(memory.Base!=null)
                foreach(var nested in StorageRegisters(memory.Base)) yield return nested;
            if(memory.Index!=null)
                foreach(var nested in StorageRegisters(memory.Index)) yield return nested;
        }
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
