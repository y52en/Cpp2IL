using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Run after stack normalization, before SSA. An ARM64 large-struct return
// writes to the caller's X8 buffer, not to X0. Only a proven stack address and
// a unique metadata signature authorize replacing the synthetic destination.
public static class HiddenStructReturnRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet) return false;
        var graph=method.ControlFlowGraph!;
        var resolver=method.AppContext.InstructionSet.CallingConventionResolver!;
        var changed=false;
        foreach(var block in graph.Blocks)
        foreach(var call in block.Instructions)
        {
            if(call.OpCode!=OpCode.Call || call.Operands[0] is not Immediate address
                || !method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue,out var targets)
                || targets.Count!=1 || !resolver.ReturnsViaHiddenBuffer(targets[0])) continue;
            var buffer=resolver.HiddenReturnBufferRegister(targets[0]);
            if(buffer is not { } register
                || ResolveStackAddress(block,block.Instructions.IndexOf(call),register) is not { } storage) continue;
            call.Destination=storage;
            call.ImplicitDefinition=new Register(null,"X0");
            changed=true;
        }
        return changed;
    }

    public static Register? ResolveStackAddress(Block block,int before,Register pointer)
        => Resolve(block,before,pointer,new HashSet<Block>(),128);

    private static Register? Resolve(Block block,int before,Register pointer,HashSet<Block> seen,int remaining)
    {
        if(remaining<=0 || !seen.Add(block)) return null;
        for(var i=before-1;i>=0;i--)
        {
            var instruction=block.Instructions[i];
            if(instruction.Destination is Register written && written.Name==pointer.Name)
            {
                if(instruction is {OpCode:OpCode.Move,Operands:[_,AddressOf {Target:Register storage}]}
                    && storage.Name.StartsWith("stack_",System.StringComparison.Ordinal)) return storage;
                if(instruction is {OpCode:OpCode.Move,Operands:[_,Register source]})
                    // The copy reads the source at this instruction, not at the
                    // eventual call. Revisit this block at an earlier position.
                    return Resolve(block,i,source,new HashSet<Block>(),remaining-1);
                return null;
            }
            if(instruction.OpCode is OpCode.NotImplemented or OpCode.Invalid or OpCode.Interrupt) return null;
            if((instruction.IsCall || instruction.OpCode==OpCode.IndirectCall) && Volatile(pointer)) return null;
        }
        if(block.Predecessors.Count!=1) return null;
        var predecessor=block.Predecessors[0];
        return Resolve(predecessor,predecessor.Instructions.Count,pointer,seen,remaining-1);
    }

    private static bool Volatile(Register register)
        => register.Name.StartsWith("V",System.StringComparison.Ordinal)
           || register.Name.StartsWith("X",System.StringComparison.Ordinal)
               && int.TryParse(register.Name.Substring(1),out var number) && number<=18;
}
