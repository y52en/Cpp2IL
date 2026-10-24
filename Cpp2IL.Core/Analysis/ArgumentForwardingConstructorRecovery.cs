using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Complete native forwarding wrappers may insert constant base arguments.
// Invert only the proven parameter/constant map. This also makes an inlined
// ancestor call a legal immediate-base initializer without inventing arguments.
public static class ArgumentForwardingConstructorRecovery
{
    public const string CacheKey="NativeConstantArgumentForwardingConstructors";
    public sealed record Argument(int Parameter,IOperand? Constant=null);
    public sealed record Template(MethodAnalysisContext Constructor,MethodAnalysisContext Called,Argument[] Arguments);

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid || constructor.Parameters.Count>8
            || constructor.DeclaringType is not {IsValueType:false} owner || owner.HasAnyGenericParameters()
            || owner.IsGenericInstance || constructor.ControlFlowGraph is not {} cfg)return null;
        var parameters=constructor.ParameterLocals.Where(l=>!l.IsThis && !l.IsMethodInfo).ToArray();
        if(parameters.Length!=constructor.Parameters.Count
            || parameters.Where((p,n)=>!TrivialConstructorRecovery.SameType(p.Type,constructor.Parameters[n].ParameterType)).Any())return null;
        var visited=new HashSet<Block>();var ordered=new List<Instruction>();var block=cfg.EntryBlock;
        while(visited.Add(block))
        {
            ordered.AddRange(block.Instructions);if(block==cfg.ExitBlock)break;
            if(block.Successors.Count!=1)return null;block=block.Successors[0];
        }
        if(!visited.Contains(cfg.ExitBlock) || cfg.Blocks.Any(b=>!visited.Contains(b)))return null;
        MethodAnalysisContext? called=null;Argument[]? bindings=null;var returned=false;
        foreach(var instruction in ordered)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(returned)return null;
            if(instruction is {OpCode:OpCode.Return,Operands.Count:0}){returned=true;continue;}
            if(called!=null || instruction is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                Operands:[MethodAnalysisContext target,LocalVariable receiver,..]}
                || !constructor.ParameterLocals.Any(p=>ReferenceEquals(p,receiver) && p.IsThis)
                || target.Name!=".ctor" || target.IsStatic || target.IsVirtual || !target.IsVoid
                || target.Parameters.Count is <1 or >8 || !Ancestor(owner,target.DeclaringType)
                || instruction.Operands.Count!=target.Parameters.Count+2)return null;
            var map=new List<Argument>();
            for(var n=0;n<target.Parameters.Count;n++)
            {
                var operand=instruction.Operands[n+2];var index=operand is LocalVariable local?Array.IndexOf(parameters,local):-1;
                if(index>=0)
                {
                    if(!TrivialConstructorRecovery.SameType(constructor.Parameters[index].ParameterType,target.Parameters[n].ParameterType))return null;
                    map.Add(new(index));
                }
                else if(Constant(target.Parameters[n].ParameterType,operand))map.Add(new(-1,operand));
                else return null;
            }
            if(!map.Any(a=>a.Constant!=null) || Enumerable.Range(0,parameters.Length).Any(p=>map.All(a=>a.Parameter!=p)))return null;
            called=target;bindings=map.ToArray();
        }
        return returned && called!=null && bindings!=null?new(constructor,called,bindings):null;
    }

    private static bool Ancestor(TypeAnalysisContext owner,TypeAnalysisContext? expected)
    {
        var seen=new HashSet<TypeAnalysisContext>();
        for(var type=owner.BaseType;type!=null && seen.Add(type) && seen.Count<=16;type=type.BaseType)
        {if(type.HasAnyGenericParameters())return false;if(TrivialConstructorRecovery.SameType(type,expected))return true;}
        return false;
    }
    private static bool Constant(TypeAnalysisContext type,IOperand value)
    {
        if(type.HasAnyGenericParameters() || type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)return false;
        if(value is StringLiteral)return type.FullName=="System.String";
        if(value is FloatLiteral)return type.FullName=="System.Single";
        if(value is DoubleLiteral)return type.FullName=="System.Double";
        if(value is not Immediate integer)return false;
        if(!type.IsValueType)return integer.Value==0;
        var scalar=type.IsEnumType?type.EnumUnderlyingType:type;
        return scalar?.FullName switch
        {
            "System.Boolean"=>integer.Value is 0 or 1,
            "System.SByte"=>integer.Value is >=sbyte.MinValue and <=sbyte.MaxValue,
            "System.Byte"=>integer.Value is >=byte.MinValue and <=byte.MaxValue,
            "System.Int16"=>integer.Value is >=short.MinValue and <=short.MaxValue,
            "System.Char" or "System.UInt16"=>integer.Value is >=ushort.MinValue and <=ushort.MaxValue,
            "System.Int32"=>integer.Value is >=int.MinValue and <=int.MaxValue,
            "System.UInt32"=>integer.Value is >=uint.MinValue and <=uint.MaxValue,
            "System.Int64"=>true,"System.UInt64"=>integer.Value>=0,_=>false
        };
    }
    private static bool Same(IOperand left,IOperand right)=>ReferenceEquals(left,right) || (left,right) switch
    {
        (Immediate a,Immediate b)=>a.Value==b.Value,
        (FloatLiteral a,FloatLiteral b)=>BitConverter.SingleToInt32Bits(a.Value)==BitConverter.SingleToInt32Bits(b.Value),
        (DoubleLiteral a,DoubleLiteral b)=>BitConverter.DoubleToInt64Bits(a.Value)==BitConverter.DoubleToInt64Bits(b.Value),
        (StringLiteral a,StringLiteral b)=>a.Value==b.Value,_=>false
    };

    private static IOperand[]? Match(Template template,Instruction call)
    {
        if(call is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false} || call.Operands.Count!=template.Arguments.Length+2
            || !ReferenceEquals(call.Operands[0],template.Called))return null;
        var args=new IOperand[template.Constructor.Parameters.Count];
        for(var n=0;n<template.Arguments.Length;n++)
        {
            var binding=template.Arguments[n];var actual=call.Operands[n+2];
            if(binding.Constant is {} constant){if(!Same(constant,actual))return null;continue;}
            if(binding.Parameter<0 || binding.Parameter>=args.Length)return null;
            if(args[binding.Parameter] is {} previous && !Same(previous,actual))return null;
            args[binding.Parameter]=actual;
        }
        return args.All(a=>a!=null)?args:null;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} cfg)return 0;var count=0;
        if(method.Name==".ctor" && !method.IsStatic && method.DeclaringType?.BaseType is {} parent
            && parent.GetExtraData<Template[]>(CacheKey) is {} parentTemplates)
        {
            var self=method.ParameterLocals.Where(p=>p.IsThis).ToArray();
            var calls=cfg.Instructions.Where(i=>i is {OpCode:OpCode.CallVoid,Operands:[MethodAnalysisContext {Name:".ctor"},LocalVariable receiver,..]}
                && self.Length==1 && ReferenceEquals(receiver,self[0])).ToArray();
            if(calls.Length==1 && Rebind(calls[0],parent,parentTemplates))count++;
        }
        foreach(var allocation in cfg.Instructions.ToArray())
        {
            if(allocation is not {OpCode:OpCode.Newobj,Operands:[LocalVariable obj,TypeAnalysisContext type]}
                || type.GetExtraData<Template[]>(CacheKey) is not {} templates)continue;
            var block=cfg.Blocks.Single(b=>b.Instructions.Contains(allocation));var origin=block;
            var at=block.Instructions.IndexOf(allocation)+1;var seen=new HashSet<Block>();var aliases=new HashSet<LocalVariable>{obj};
            var finished=false;
            while(seen.Add(block) && !finished)
            {
                foreach(var call in block.Instructions.Skip(at))
                {
                    if(call.OpCode is OpCode.Nop or OpCode.Jump)continue;
                    if(call is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]} && aliases.Contains(source))
                    {if(!aliases.Add(alias)){finished=true;break;}continue;}
                    finished=true;
                    if(call is not {OpCode:OpCode.CallVoid,Operands:[MethodAnalysisContext,LocalVariable receiver,..]} || !aliases.Contains(receiver))break;
                    DominatorInfo? dominance=null;
                    var all=cfg.Instructions;var index=all.IndexOf(allocation);
                    if(Rebind(call,type,templates,args=>args.All(a=>InlinedConstructorRecovery.AvailableBeforeAllocation(
                        a,method,all,index,origin,ref dominance,aliases))))count++;
                    break;
                }
                if(finished || block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)break;
                block=block.Successors[0];at=0;
            }
        }
        return count;
    }
    private static bool Rebind(Instruction call,TypeAnalysisContext owner,Template[] templates,Func<IOperand[],bool>? available=null)
    {
        var matches=templates.Where(t=>ReferenceEquals(t.Constructor.DeclaringType,owner))
            .Select(t=>(Template:t,Args:Match(t,call))).Where(p=>p.Args!=null).ToArray();
        if(matches.Length!=1 || available!=null && !available(matches[0].Args!))return false;
        call.SetOperands(new List<IOperand>{matches[0].Template.Constructor,call.Operands[1]}.Concat(matches[0].Args!).ToList());
        return true;
    }
}
