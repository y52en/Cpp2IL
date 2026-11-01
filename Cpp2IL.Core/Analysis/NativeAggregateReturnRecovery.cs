using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Complete original PLT stubs/unique import relocations are archived in2375;
// complete memcpy caller C is2374. The relocated WHOLE-image fingerprint gates
// these addresses. Never treat an arbitrary similarly named call as memcpy.
public static class NativeAggregateReturnRecovery
{
    private const ulong Copy=0xA5FC30,Zero=0xA5FF10;

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph || !graph.Instructions.Any(i=>i is
            {OpCode:OpCode.Call,Operands:[Immediate {UnsignedValue:Copy or Zero},..]})
            || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        var changed=graph.Instructions.ToArray().Count(call=>TryRewrite(method,call,true));
        if(changed>0)DeadCodeEliminator.Run(method);
        return changed;
    }

    internal static bool TryRewrite(MethodAnalysisContext method,Instruction call,bool reviewedImage)
    {
        if(!reviewedImage || method.ControlFlowGraph is not {} graph || graph.Instructions.Any(i=>i.OpCode==OpCode.IndirectJump)
            || call is not {OpCode:OpCode.Call,NativeVirtualDispatch:false,Operands:[Immediate address,
                LocalVariable result,LocalVariable {IsReturnBuffer:true} destination,var source,Immediate bytes,..]}
            || address.UnsignedValue is not (Copy or Zero)
            || call.Operands.Skip(5).Any(o=>o is not (LocalVariable or Immediate)))return false;
        var type=method.ReturnType;
        if(!type.IsValueType || type.HasAnyGenericParameters() || TypeSizes.IsScalarValueType(type)
            || !TrivialConstructorRecovery.SameType(type,destination.Type)
            || !TrivialConstructorRecovery.SameType(type,result.Type)
            || method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method)==null)return false;
        var pointerSize=method.AppContext.Binary.PointerSizeBytes;
        var size=type is GenericInstanceTypeAnalysisContext
            ? ClosedGenericValueLayout.TryGet(type,pointerSize)?.Size??0
            : TypeSizes.UnboxedSize(type,pointerSize);
        if(size is <=0 or >4096 || bytes.Value!=size)return false;
        var all=graph.Instructions.ToArray();
        var blocks=graph.Blocks.Where(b=>b.Instructions.Contains(call)).ToArray();
        if(blocks.Length!=1)return false;
        var tail=blocks[0].Instructions.Skip(blocks[0].Instructions.IndexOf(call)+1).Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(tail is not [{OpCode:OpCode.Return,Operands:[var returned]}] || !ReferenceEquals(returned,result)
            || all.Count(i=>ReferenceEquals(i.Destination,result))!=1
            || all.Any(i=>!ReferenceEquals(i,call)&&!ReferenceEquals(i,tail[0])
                && InterfaceDispatchRecovery.UsedLocals(i).Contains(result)))return false;
        IOperand? value=null;
        if(address.UnsignedValue==Zero)
        {
            if(source is not Immediate {Value:0})return false;
            value=new DefaultStructValue(type);
        }
        else if(source is AddressOf {Target:LocalVariable local} && TrivialConstructorRecovery.SameType(local.Type,type))value=local;
        else if(source is AddressOf {Target:FieldReference {Field:{} field} reference}
            && TrivialConstructorRecovery.SameType(field.FieldType,type))value=reference;
        else if(source is AddressOf {Target:ArrayAccess {Array.Type:SzArrayTypeAnalysisContext {ElementType:var element}} access}
            && TrivialConstructorRecovery.SameType(element,type) && GuardedArrayRead(graph,call,access))value=access;
        else
        {
            var definitions=all.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
                .ToDictionary(g=>g.Key,g=>g.Count()==1?(Instruction?)g.Single():null);
            var resolvedAccess=ArrayRecovery.MatchFullStructPointer(source,type,method.AppContext.Binary.PointerSizeBytes,definitions);
            if(resolvedAccess!=null && GuardedArrayRead(graph,call,resolvedAccess))value=resolvedAccess;
        }
        if(value==null)return false;
        // Only the reviewed native tail copy changes. Existing null/bounds,
        // loop, exception and source-side effects stay in their original blocks.
        call.OpCode=OpCode.Move;
        call.SetOperands(result,value);
        call.NativeReadSize=call.NativeWriteSize=0;
        return true;
    }

    private static bool GuardedArrayRead(ISILControlFlowGraph graph,Instruction call,ArrayAccess access)
    {
        var all=graph.Instructions.ToArray();
        if(graph.Blocks.Count>256 || all.Length>8192)return false;
        var defs=all.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .ToDictionary(g=>g.Key,g=>g.Count()==1?g.Single():null);
        var callBlock=graph.Blocks.Single(b=>b.Instructions.Contains(call));
        var dominance=new DominatorInfo(graph);
        bool Same(IOperand left,IOperand right)=>ReferenceEquals(left,right)
            || left is Immediate a && right is Immediate b && a.Value==b.Value;
        foreach(var block in graph.Blocks)
        {
            if(block.Instructions.LastOrDefault() is not {OpCode:OpCode.ConditionalJump,Operands:[Block target,var condition]} branch
                || block.Successors.Count!=2 || !block.Successors.Contains(target)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph,branch,call))continue;
            var inverted=false;var seen=new HashSet<LocalVariable>();Instruction? compare=null;
            while(condition is LocalVariable flag && seen.Add(flag) && defs.TryGetValue(flag,out var definition) && definition!=null)
            {
                if(definition is {OpCode:OpCode.Not,Operands:[_,var operand]}){inverted=!inverted;condition=operand;continue;}
                compare=definition;break;
            }
            if(compare is not {OpCode:OpCode.CheckLess,UnsignedComparison:true,Operands:[_,var index,LocalVariable length]}
                || !Same(index,access.Index) || !defs.TryGetValue(length,out var load)
                || load is not {OpCode:OpCode.Move,Operands:[_,ArrayLength arrayLength]}
                || !ReferenceEquals(arrayLength.Array,access.Array)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph,load,compare)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph,compare,branch))continue;
            var success=inverted?block.Successors.Single(b=>!ReferenceEquals(b,target)):target;
            if(!dominance.Dominates(success,callBlock))continue;
            var protectedLocals=new HashSet<LocalVariable>{access.Array,length};
            if(access.Index is LocalVariable indexed)protectedLocals.Add(indexed);
            if(all.Any(i=>i.Operands.OfType<AddressOf>().Any(a=>a.Target is LocalVariable local && protectedLocals.Contains(local))))continue;
            // The retained length load dereferences this SAME array and
            // therefore already preserves its null exception. Prove stability
            // from that load, not just from the successful bounds edge: a
            // write between length/compare/branch must not validate a new array.
            var loadBlocks=graph.Blocks.Where(b=>b.Instructions.Contains(load)).ToArray();
            if(loadBlocks.Length!=1)continue;
            var loadBlock=loadBlocks[0];
            var queue=new Queue<Block>();var visited=new HashSet<Block>();queue.Enqueue(loadBlock);
            var stable=true;var reached=false;
            while(queue.TryDequeue(out var next) && stable)
            {
                if(!visited.Add(next))continue;
                foreach(var instruction in next.Instructions.Skip(ReferenceEquals(next,loadBlock)
                    ?next.Instructions.IndexOf(load)+1:0))
                {
                    if(ReferenceEquals(instruction,call)){reached=true;break;}
                    if(instruction.Destination is LocalVariable written && protectedLocals.Contains(written))
                    {stable=false;break;}
                    if(instruction.Operands.OfType<AddressOf>().Any(a=>a.Target is LocalVariable local && protectedLocals.Contains(local)))
                    {stable=false;break;}
                }
                if(!ReferenceEquals(next,callBlock))foreach(var child in next.Successors)queue.Enqueue(child);
            }
            if(stable && reached)return true;
        }
        return false;
    }
}
