using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Reconstitute the immediate parent from its COMPLETE original native body,
// including constant stores before its base call and parameter stores after it.
// This does not delete a guessed ancestor call or widen field visibility.
public static class ParameterizedBaseInitializerRecovery
{
    public const string CacheKey="NativeParameterizedBaseInitializerTemplates";
    public sealed record Store(FieldAnalysisContext Field,int Width,int Parameter,IOperand? Constant);
    public sealed record Template(MethodAnalysisContext Constructor,MethodAnalysisContext Ancestor,
        int BasePosition,Store[] Stores);

    private static bool ClosedClass(TypeAnalysisContext type)=>!type.IsValueType && !type.HasAnyGenericParameters();
    private static bool Owns(TypeAnalysisContext owner,FieldAnalysisContext field)
    {
        var seen=new HashSet<TypeAnalysisContext>();
        for(var type=owner;type!=null && seen.Count<64 && seen.Add(type);type=type.BaseType)
        {
            if(!ClosedClass(type))return false;
            if(ReferenceEquals(type,field.DeclaringType))return type.Fields.Contains(field) && !field.IsStatic;
        }
        return false;
    }
    private static int Width(TypeAnalysisContext type,int pointer)
    {
        if(type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext || type.HasAnyGenericParameters())return 0;
        if(!type.IsValueType)return pointer;
        return (type.IsEnumType?type.EnumUnderlyingType:type)?.FullName switch {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32" or "System.Single"=>4,
            "System.Int64" or "System.UInt64" or "System.Double" or "System.IntPtr" or "System.UIntPtr"=>8,_=>0};
    }
    private static bool Constant(TypeAnalysisContext type,IOperand value)=>value switch {
        Immediate n=>!type.IsValueType?n.Value==0:(type.IsEnumType?type.EnumUnderlyingType:type)?.FullName is
            "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char" or "System.Int16" or "System.UInt16"
            or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr",
        FloatLiteral=>type.FullName=="System.Single",DoubleLiteral=>type.FullName=="System.Double",_=>false};
    private static bool SameConstant(IOperand a,IOperand b,int width)=>(a,b)switch {
        (Immediate x,Immediate y)=>((ulong)x.Value&(width==8?ulong.MaxValue:(1UL<<(width*8))-1))
            ==((ulong)y.Value&(width==8?ulong.MaxValue:(1UL<<(width*8))-1)),
        (FloatLiteral x,FloatLiteral y)=>BitConverter.SingleToInt32Bits(x.Value)==BitConverter.SingleToInt32Bits(y.Value),
        (DoubleLiteral x,DoubleLiteral y)=>BitConverter.DoubleToInt64Bits(x.Value)==BitConverter.DoubleToInt64Bits(y.Value),_=>false};
    private static List<Instruction>? Linear(ISILControlFlowGraph cfg)
    {
        var seen=new HashSet<Block>();var block=cfg.EntryBlock;var rows=new List<Instruction>();
        while(seen.Add(block))
        {
            rows.AddRange(block.Instructions.Where(i=>i.OpCode is not (OpCode.Nop or OpCode.Jump)));
            if(ReferenceEquals(block,cfg.ExitBlock))return cfg.Blocks.All(seen.Contains)?rows:null;
            if(block.Successors.Count!=1)return null;block=block.Successors[0];
        }
        return null;
    }
    private static bool AncestorCall(TypeAnalysisContext owner,MethodAnalysisContext target)
        =>target.Name==".ctor" && !target.IsStatic && !target.IsVirtual && target.IsVoid && target.Parameters.Count==0
            && TrivialConstructorRecovery.SameType(owner.BaseType,target.DeclaringType)
            && (target.DeclaringType?.FullName!="System.Object"
                || target.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey)is{IsNoOp:true});

    // A child's own primitive constant store may be interleaved with the
    // parent's stores. Keep it on the SAME side of the ancestor call and only
    // commute it with disjoint parent stores: no callback, read or barrier moves.
    private static bool CommutingOwnStore(Instruction i,TypeAnalysisContext owner,LocalVariable self,Template template)
    {
        if((owner.Attributes&System.Reflection.TypeAttributes.ExplicitLayout)!=0
            || i.ImplicitDefinition!=null
            || i is not{OpCode:OpCode.Move,Operands:[FieldReference{Parent:null} field,var value]}
            || !ReferenceEquals(field.Local,self) || !ReferenceEquals(field.Field.DeclaringType,owner)
            || !owner.Fields.Contains(field.Field) || field.Field.IsStatic || field.Offset!=field.Field.Offset
            || field.Offset<16 || !field.Field.FieldType.IsValueType
            || !Constant(field.Field.FieldType,value) || i.NativeWriteSize is <1 or >8
            || i.NativeWriteSize!=Width(field.Field.FieldType,owner.AppContext.Binary.PointerSizeBytes))return false;
        return template.Stores.All(s=>(long)field.Offset+i.NativeWriteSize<=s.Field.Offset
            || (long)s.Field.Offset+s.Width<=field.Offset);
    }

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid
            || constructor.Parameters.Count is <1 or >8 || constructor.DeclaringType is not {} owner
            || !ClosedClass(owner) || owner.BaseType is not {} parent || !ClosedClass(parent)
            || constructor.ControlFlowGraph is not {} cfg || Linear(cfg)is not {} body)return null;
        var selves=constructor.ParameterLocals.Where(p=>p.IsThis).ToArray();
        var parameters=constructor.ParameterLocals.Where(p=>!p.IsThis && !p.IsMethodInfo).ToArray();
        if(selves.Length!=1 || !TrivialConstructorRecovery.SameType(selves[0].Type,owner)
            || parameters.Length!=constructor.Parameters.Count
            || parameters.Where((p,n)=>!TrivialConstructorRecovery.SameType(p.Type,constructor.Parameters[n].ParameterType)).Any())return null;
        var stores=new List<Store>();MethodAnalysisContext? ancestor=null;var position=-1;var returned=false;
        foreach(var i in body)
        {
            if(returned)return null;
            if(i is{OpCode:OpCode.Return,Operands.Count:0}){returned=true;continue;}
            if(i is{OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,NativeNullCheckedCall:false,
                    Operands:[MethodAnalysisContext target,LocalVariable receiver]}
                && ReferenceEquals(receiver,selves[0]) && AncestorCall(owner,target) && ancestor==null)
            {ancestor=target;position=stores.Count;continue;}
            if(i is not{OpCode:OpCode.Move,Operands:[FieldReference{Parent:null} field,var value]}
                || !ReferenceEquals(field.Local,selves[0]) || !Owns(owner,field.Field)
                || field.Offset!=field.Field.Offset || field.Offset<16
                || Width(field.Field.FieldType,constructor.AppContext.Binary.PointerSizeBytes)is not >0
                || i.NativeWriteSize!=Width(field.Field.FieldType,constructor.AppContext.Binary.PointerSizeBytes)
                || stores.Any(s=>ReferenceEquals(s.Field,field.Field)))return null;
            var parameter=value is LocalVariable local?Array.IndexOf(parameters,local):-1;
            if(parameter>=0)
            {
                if(!TrivialConstructorRecovery.SameType(field.Field.FieldType,constructor.Parameters[parameter].ParameterType))return null;
                stores.Add(new(field.Field,i.NativeWriteSize,parameter,null));
            }
            else if(Constant(field.Field.FieldType,value))stores.Add(new(field.Field,i.NativeWriteSize,-1,value));
            else return null;
        }
        return returned && ancestor!=null && stores.Count>0
            && Enumerable.Range(0,parameters.Length).All(p=>stores.Any(s=>s.Parameter==p))
            ?new(constructor,ancestor,position,stores.ToArray()):null;
    }

    public static int Run(MethodAnalysisContext method)=>method.AppContext.UnityVersion.Major==2018
        && method.AppContext.UnityVersion.Minor==4 && method.AppContext.Binary.PointerSizeBytes==8
        && method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet?Recover(method):0;

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.Name!=".ctor" || method.IsStatic || !method.IsVoid || method.DeclaringType is not{} owner
            || !ClosedClass(owner) || owner.BaseType is not{} parent || !ClosedClass(parent)
            || parent.GetExtraData<Template[]>(CacheKey)is not{Length:>0} templates
            || method.ControlFlowGraph is not{} cfg || cfg.EntryBlock.Predecessors.Count!=0)return 0;
        var selves=method.ParameterLocals.Where(p=>p.IsThis).ToArray();
        if(selves.Length!=1 || !TrivialConstructorRecovery.SameType(selves[0].Type,owner))return 0;
        var self=selves[0];
        if(cfg.Instructions.Any(i=>ReferenceEquals(i.Destination,self)
            || i.ImplicitDefinition is{} register && register.Name==self.Register.Name && register.Number==self.Register.Number))return 0;
        var calls=cfg.Instructions.Where(i=>i.IsCall && i.Operands.Count>(i.OpCode==OpCode.Call?2:1)
            && i.Operands[0]is MethodAnalysisContext{Name:".ctor"}
            && ReferenceEquals(i.Operands[i.OpCode==OpCode.Call?2:1],self)).ToArray();
        if(calls.Length!=1 || calls[0]is not{OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,NativeNullCheckedCall:false,
            Operands:[MethodAnalysisContext called,LocalVariable receiver]} || !ReferenceEquals(receiver,self))return 0;
        var call=calls[0];var prefix=new List<Instruction>();var seen=new HashSet<Block>();var block=cfg.EntryBlock;
        while(seen.Add(block))
        {
            if(!ReferenceEquals(block,cfg.EntryBlock) && block.Predecessors.Count!=1)break;
            prefix.AddRange(block.Instructions.Where(i=>i.OpCode is not(OpCode.Nop or OpCode.Jump)));
            if(prefix.Count>512 || block.Successors.Count!=1)break;block=block.Successors[0];
        }
        if(prefix.Count>512)return 0;
        var matches=new List<(Template Template,Instruction[] Stores,IOperand[] Arguments)>();
        foreach(var template in templates)
        {
            if(!ReferenceEquals(template.Constructor.DeclaringType,parent) || !ReferenceEquals(template.Ancestor,called)
                || !AncestorCall(parent,called) || template.BasePosition<0 || template.BasePosition>template.Stores.Length)continue;
            var before=prefix.IndexOf(call)-1;var needed=template.BasePosition;
            while(before>=0 && needed>0)
            {
                if(!CommutingOwnStore(prefix[before],owner,self,template))needed--;
                before--;
            }
            if(needed!=0)continue;
            var start=before+1;
            if(start<0 || start+template.Stores.Length+1>prefix.Count)continue;
            if(prefix.Take(start).Any(i=>i is{OpCode:OpCode.Move,Operands:[MemoryOperand,..]}
                || i is{OpCode:OpCode.Move,Operands:[FieldReference field,..]}
                    && (!ReferenceEquals(field.Local,self)||field.Parent!=null||!ReferenceEquals(field.Field.DeclaringType,owner))))continue;
            var matched=new List<Instruction>();var args=new IOperand[template.Constructor.Parameters.Count];var valid=true;var storeIndex=0;
            var cursor=start;
            for(var n=0;n<template.Stores.Length+1;n++)
            {
                while(cursor<prefix.Count && CommutingOwnStore(prefix[cursor],owner,self,template))cursor++;
                if(cursor>=prefix.Count){valid=false;break;}
                var i=prefix[cursor++];
                if(n==template.BasePosition){if(!ReferenceEquals(i,call))valid=false;continue;}
                var expected=template.Stores[storeIndex++];
                if(i is not{OpCode:OpCode.Move,Operands:[FieldReference{Parent:null} field,var value]}
                    || !ReferenceEquals(field.Local,self) || !ReferenceEquals(field.Field,expected.Field)
                    || field.Offset!=expected.Field.Offset || i.NativeWriteSize!=expected.Width){valid=false;break;}
                if(expected.Constant is{} constant)
                {if(!SameConstant(value,constant,expected.Width)){valid=false;break;}}
                else
                {
                    if(expected.Parameter<0 || expected.Parameter>=args.Length || value is not LocalVariable local
                        || ReferenceEquals(local,self) || !TrivialConstructorRecovery.SameType(local.Type,template.Constructor.Parameters[expected.Parameter].ParameterType))
                    {valid=false;break;}
                    var definitions=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,local)).ToArray();
                    if(!method.ParameterLocals.Contains(local) && (definitions.Length!=1 || !prefix.Take(start).Contains(definitions[0])))
                    {valid=false;break;}
                    if(args[expected.Parameter]!=null && !ReferenceEquals(args[expected.Parameter],value)){valid=false;break;}
                    args[expected.Parameter]=value;
                }
                matched.Add(i);
            }
            if(valid && args.All(a=>a!=null))matches.Add((template,matched.ToArray(),args));
        }
        if(matches.Count!=1)return 0;
        var chosen=matches[0];call.SetOperands([chosen.Template.Constructor,self,..chosen.Arguments]);
        foreach(var store in chosen.Stores){store.OpCode=OpCode.Nop;store.SetOperands();}
        foreach(var b in cfg.Blocks)b.CalculateBlockType();return 1;
    }
}
