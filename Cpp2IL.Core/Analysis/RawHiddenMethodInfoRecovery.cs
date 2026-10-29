using System;
using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

// Pre-SSA counterpart of the existing authoritative metadata-usage/GOT lookup.
// Reads one reaching register definition. Merges, unknown pointer arithmetic and
// volatile clobbers remain unresolved; an unused register is not a method proof.
internal static class RawHiddenMethodInfoRecovery
{
    internal static MethodAnalysisContext? Resolve(MethodAnalysisContext caller,Block block,int before,Register register,
        Func<ulong,MethodAnalysisContext?>? metadata=null,Func<ulong,ulong?>? got=null)
    {
        metadata??=address=>
        {
            var usage=caller.AppContext.LibCpp2IlContext.GetMethodGlobalByAddress(address);
            return usage?.Type is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef
                ?caller.AppContext.ResolveContextForMethod(usage):null;
        };
        got??=address=>caller.AppContext.Binary is ElfFile elf&&elf.IsGlobalOffsetTableEntry(address)
            ?elf.ReadPointerAtVirtualAddress(address):null;
        var seen=new HashSet<(Block,int,string)>();
        (Block Block,int Index,IOperand Value)? Definition(Block current,int limit,Register wanted,int budget)
        {
            if(budget<=0 || !seen.Add((current,limit,wanted.Name)))return null;
            for(var index=limit-1;index>=0;index--)
            {
                var instruction=current.Instructions[index];
                if(instruction.Destination is Register destination&&destination.Name==wanted.Name)
                    return instruction is {OpCode:OpCode.Move,Operands:[_,var value]}?(current,index,value):null;
                if(instruction.ImplicitDefinition?.Name==wanted.Name
                    || instruction.OpCode is OpCode.Invalid or OpCode.NotImplemented or OpCode.Interrupt
                    || (instruction.IsCall||instruction.OpCode==OpCode.IndirectCall)&&Volatile(wanted))return null;
            }
            return current.Predecessors.Count==1
                ?Definition(current.Predecessors[0],current.Predecessors[0].Instructions.Count,wanted,budget-1):null;
        }
        MethodAnalysisContext? Follow(Block current,int limit,Register wanted,int budget)
        {
            if(budget<=0||Definition(current,limit,wanted,budget)is not {} definition)return null;
            return definition.Value switch
            {
                RuntimeMethodInfoAnalysisContext info=>info.RepresentedMethod,
                Register alias=>Follow(definition.Block,definition.Index,alias,budget-1),
                MemoryOperand{Base:null,Index:null,Scale:0} cell=>metadata(unchecked((ulong)cell.Addend)),
                MemoryOperand{Base:Register pointer,Index:null,Scale:0,Addend:0}=>Pointer(definition.Block,definition.Index,pointer,budget-1)is {} address?metadata(address):null,
                _=>null
            };
        }
        ulong? Pointer(Block current,int limit,Register wanted,int budget)
        {
            if(budget<=0||Definition(current,limit,wanted,budget)is not {} definition)return null;
            return definition.Value switch
            {
                Register alias=>Pointer(definition.Block,definition.Index,alias,budget-1),
                MemoryOperand{Base:null,Index:null,Scale:0} slot=>got(unchecked((ulong)slot.Addend)),
                _=>null
            };
        }
        try{return Follow(block,before,register,64);}catch(Exception){return null;}
    }

    private static bool Volatile(Register register)
        =>register.Name.StartsWith("V",StringComparison.Ordinal)
            || register.Name.StartsWith("X",StringComparison.Ordinal)
                &&int.TryParse(register.Name[1..],out var number)&&number<=18;
}
