using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// An optimized nonvirtual instance callee can ignore its incoming X0 entirely.
// Do not generate a throwing cross-type cast for that dead argument. Only the
// caller's existing, same-owner non-null `this` is an authorized substitute.
public static class UnusedInstanceReceiverRecovery
{
    private sealed record Proof(bool Unused);
    private static readonly ConditionalWeakTable<MethodAnalysisContext,Proof> Proofs=new();

    public static bool EntryX0Unused(ISILControlFlowGraph graph)
    {
        var pending=new Queue<Block>();var visited=new HashSet<Block>();
        pending.Enqueue(graph.EntryBlock);
        while(pending.Count>0)
        {
            var block=pending.Dequeue();if(!visited.Add(block))continue;
            var killed=false;
            foreach(var instruction in block.Instructions)
            {
                if(instruction.OpCode==OpCode.Invalid)return false;
                var destinationIndex=instruction.OpCode is OpCode.Call or OpCode.IndirectCall ? 1 : 0;
                for(var i=0;i<instruction.Operands.Count;i++)
                {
                    if(i==destinationIndex && instruction.Destination is Register
                        && instruction.Operands[i] is Register)continue;
                    if(ReadsX0(instruction.Operands[i]))return false;
                }
                if(instruction.Destination is Register {Name:"X0"}
                    || instruction.ImplicitDefinition is {Name:"X0"})
                {killed=true;break;}
            }
            if(!killed)foreach(var successor in block.Successors)pending.Enqueue(successor);
        }
        return true;
    }

    private static bool ReadsX0(IOperand? operand)=>operand switch
    {
        Register {Name:"X0"}=>true,
        MemoryOperand memory=>ReadsX0(memory.Base)||ReadsX0(memory.Index),
        AddressOf address=>ReadsX0(address.Target),
        _=>false
    };

    private static bool Prove(MethodAnalysisContext target)
    {
        if(target.UnderlyingPointer==0 || target.IsStatic || target.IsVirtual
            || target.Name is ".ctor" or ".cctor" || target.DeclaringType?.IsValueType!=false
            || target.DeclaringType.HasAnyGenericParameters() || target.GenericParameters.Count!=0
            || target.AppContext.InstructionSet is not NewArmV8InstructionSet
            || target.AppContext.Binary.PointerSizeBytes!=8)return false;
        try
        {
            // Raw lifted registers, BEFORE SSA, type inference, copy folding,
            // dead-code deletion or call argument trimming. Every read of the
            // entry value rejects, including saving it in another register.
            var raw=target.AppContext.InstructionSet.GetIsilFromMethod(target);
            return raw.Count>0 && EntryX0Unused(new ISILControlFlowGraph(raw));
        }
        catch(Exception){return false;}
    }

    public static int Run(MethodAnalysisContext caller)
    {
        if(caller.IsStatic || caller.ControlFlowGraph==null || caller.DeclaringType?.IsValueType!=false
            || caller.DeclaringType.HasAnyGenericParameters())return 0;
        var selves=caller.ParameterLocals.Where(l=>l.IsThis).ToArray();
        if(selves.Length!=1)return 0;
        var self=selves[0];
        var count=0;
        foreach(var call in caller.ControlFlowGraph.Instructions)
        {
            if(!call.IsCall || call.NativeVirtualDispatch || call.Operands[0] is not MethodAnalysisContext target
                || !TrivialConstructorRecovery.SameType(target.DeclaringType,caller.DeclaringType))continue;
            var receiverIndex=call.OpCode==OpCode.Call ? 2 : 1;
            if(call.Operands.Count<=receiverIndex || ReferenceEquals(call.Operands[receiverIndex],self)
                || !Proofs.GetValue(target,t=>new Proof(Prove(t))).Unused)continue;
            call.SetOperand(receiverIndex,self);
            if(!caller.Locals.Contains(self))caller.Locals.Add(self);
            count++;
        }
        return count;
    }
}
