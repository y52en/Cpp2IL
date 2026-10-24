using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A derived constructor may be a complete native tail-forwarder to its direct
// base. Bind the ALLOCATED derived owner only after proving the whole wrapper;
// never emit new Base() for a Derived allocation or discard base effects.
public static class ForwardedConstructorRecovery
{
    public const string CacheKey = "NativeParameterForwardingConstructors";
    public sealed record Template(MethodAnalysisContext Constructor, MethodAnalysisContext Base);

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid
            || constructor.Parameters.Count is <1 or >8 || constructor.DeclaringType is not {} type
            || type.IsValueType || type.HasAnyGenericParameters() || type.BaseType is not {} parent
            || parent.HasAnyGenericParameters() || constructor.ControlFlowGraph is not {} cfg)return null;
        var args=constructor.ParameterLocals.Where(l=>!l.IsThis && !l.IsMethodInfo).ToArray();
        if(args.Length!=constructor.Parameters.Count)return null;
        if(args.Where((a,n)=>!TrivialConstructorRecovery.SameType(a.Type,constructor.Parameters[n].ParameterType)).Any())return null;
        var visited=new HashSet<Block>();var block=cfg.EntryBlock;var ordered=new List<Instruction>();
        while(visited.Add(block))
        {
            ordered.AddRange(block.Instructions);
            if(ReferenceEquals(block,cfg.ExitBlock))break;
            if(block.Successors.Count!=1)return null;
            block=block.Successors[0];
        }
        if(!visited.Contains(cfg.ExitBlock) || cfg.Blocks.Any(b=>!visited.Contains(b)))return null;
        MethodAnalysisContext? forwarded=null;var returned=false;
        foreach(var instruction in ordered)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(returned)return null;
            if(instruction is {OpCode:OpCode.Return,Operands.Count:0}){returned=true;continue;}
            if(forwarded!=null || instruction is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                Operands:[MethodAnalysisContext target,LocalVariable receiver,..]}
                || !constructor.ParameterLocals.Any(p=>ReferenceEquals(p,receiver) && p.IsThis)
                || target.Name!=".ctor" || target.IsStatic || target.IsVirtual || !target.IsVoid
                || !ProvenAncestor(type,target.DeclaringType)
                || target.Parameters.Count!=args.Length || instruction.Operands.Count!=args.Length+2)return null;
            for(var n=0;n<args.Length;n++)
                if(!ReferenceEquals(instruction.Operands[n+2],args[n])
                    || !ExactOrClassUpcast(constructor.Parameters[n].ParameterType,target.Parameters[n].ParameterType))return null;
            forwarded=target;
        }
        return returned && forwarded!=null?new(constructor,forwarded):null;
    }

    // A complete native forwarding wrapper may pass XElement to XContainer.
    // This is an implicit non-boxing reference upcast, NOT parameter identity.
    // Restrict new support to an exact metadata base-class chain: no interface,
    // array covariance, numeric conversion, generic variance or name matching.
    private static bool ExactOrClassUpcast(TypeAnalysisContext? source,TypeAnalysisContext? target)
    {
        if(TrivialConstructorRecovery.SameType(source,target))return true;
        if(source==null || target==null || source.IsValueType || target.IsValueType
            || source.IsInterface || target.IsInterface || source.HasAnyGenericParameters() || target.HasAnyGenericParameters()
            || source is GenericInstanceTypeAnalysisContext or SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext
                or ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            || target is GenericInstanceTypeAnalysisContext or SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext
                or ByRefTypeAnalysisContext or PointerTypeAnalysisContext)return false;
        var seen=new HashSet<TypeAnalysisContext>{source};
        for(var parent=source.BaseType;parent!=null && seen.Add(parent) && seen.Count<=32;parent=parent.BaseType)
        {
            if(parent.HasAnyGenericParameters() || parent.IsGenericInstance || parent.IsValueType || parent.IsInterface)return false;
            if(TrivialConstructorRecovery.SameType(parent,target))return true;
        }
        return false;
    }

    private static bool NarrowedArgumentsProven(Template template,Instruction call)
    {
        for(var n=0;n<template.Constructor.Parameters.Count;n++)
        {
            var expected=template.Constructor.Parameters[n].ParameterType;
            if(TrivialConstructorRecovery.SameType(expected,template.Base.Parameters[n].ParameterType))continue;
            var actual=call.Operands[n+2];
            if(actual is Immediate {Value:0} && !expected.IsValueType)continue;
            var type=actual switch {LocalVariable local=>local.Type,FieldReference field=>field.Field.FieldType,_=>null};
            // Rebinding must not turn a base-typed argument into a downcast.
            if(!ExactOrClassUpcast(type,expected))return false;
        }
        return true;
    }

    // The original native wrapper may already inline an intermediate base's
    // own forwarding wrapper. The COMPLETE body still proves the exact target
    // and argument order; an unrelated owner/signature is never sufficient.
    private static bool ProvenAncestor(TypeAnalysisContext owner,TypeAnalysisContext? expected)
    {
        var seen=new HashSet<TypeAnalysisContext>();
        for(var type=owner.BaseType;type!=null && seen.Add(type) && seen.Count<=16;type=type.BaseType)
        {
            if(type.HasAnyGenericParameters())return false;
            if(TrivialConstructorRecovery.SameType(type,expected))return true;
        }
        return false;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph==null)return 0;var count=0;
        foreach(var allocation in method.ControlFlowGraph.Instructions.ToArray())
            if(allocation is {OpCode:OpCode.Newobj,Operands:[LocalVariable,TypeAnalysisContext type]}
                && type.GetExtraData<Template[]>(CacheKey) is {Length:>0} templates
                && Recover(method,allocation,templates))count++;
        return count;
    }

    public static bool Recover(MethodAnalysisContext method,Instruction allocation,IReadOnlyList<Template> templates)
    {
        if(method.ControlFlowGraph is not {} cfg || allocation.Operands is not [LocalVariable obj,TypeAnalysisContext type])return false;
        var all=cfg.Instructions;var index=all.IndexOf(allocation);if(index<0)return false;
        var origin=cfg.Blocks.Single(b=>b.Instructions.Contains(allocation));var block=origin;
        var start=block.Instructions.IndexOf(allocation)+1;var visited=new HashSet<Block>();var aliases=new HashSet<LocalVariable>{obj};
        while(visited.Add(block))
        {
            foreach(var instruction in block.Instructions.Skip(start))
            {
                if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
                if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]} && aliases.Contains(source))
                {if(!aliases.Add(alias))return false;continue;}
                if(instruction is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                    Operands:[MethodAnalysisContext target,LocalVariable receiver,..]} || !aliases.Contains(receiver))return false;
                var matches=templates.Where(t=>ReferenceEquals(t.Constructor.DeclaringType,type)
                    && ReferenceEquals(t.Base,target) && instruction.Operands.Count==t.Constructor.Parameters.Count+2
                    && NarrowedArgumentsProven(t,instruction)).ToArray();
                if(matches.Length!=1)return false;
                DominatorInfo? dominance=null;
                if(instruction.Operands.Skip(2).Any(value=>!InlinedConstructorRecovery.AvailableBeforeAllocation(
                    value,method,all,index,origin,ref dominance,aliases)))return false;
                instruction.SetOperand(0,matches[0].Constructor);return true;
            }
            if(block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)return false;
            block=block.Successors[0];start=0;
        }
        return false;
    }
}
