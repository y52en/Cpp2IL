using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Exact native templates for inlined parameterless field initializers. Unlike
// the trivial-ctor pass, every constant field write must match and is consumed.
public static class ConstantFieldConstructorRecovery
{
    public const string CacheKey="NativeConstantFieldConstructorTemplates";
    public enum ConstantKind { Integral,Single,Double }
    public sealed record Store(FieldAnalysisContext Field,long Value,int Width,ConstantKind Kind=ConstantKind.Integral);
    public sealed record Template(MethodAnalysisContext Constructor,IReadOnlyList<Store> Stores,
        MethodAnalysisContext? BaseConstructor=null,int BaseStoreIndex=-1);

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid || constructor.Parameters.Count!=0
            || constructor.DeclaringType is not {IsValueType:false,GenericParameters.Count:0} owner
            || owner is GenericInstanceTypeAnalysisContext || owner.BaseType==null
            || constructor.ControlFlowGraph is not { } cfg)return null;
        var seen=new HashSet<Block>();var current=cfg.EntryBlock;var ordered=new List<Instruction>();
        while(seen.Add(current))
        {
            ordered.AddRange(current.Instructions);
            if(ReferenceEquals(current,cfg.ExitBlock))break;
            if(current.Successors.Count!=1)return null;
            current=current.Successors[0];
        }
        if(!ReferenceEquals(current,cfg.ExitBlock) || cfg.Blocks.Any(b=>!seen.Contains(b)))return null;
        var stores=new List<Store>();var baseSeen=false;var baseStoreIndex=-1;var returned=false;MethodAnalysisContext? baseConstructor=null;
        foreach(var instruction in ordered)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(returned)return null;
            if(instruction is {OpCode:OpCode.Return,Operands.Count:0})
            {returned=true;continue;}
            if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                    Operands:[MethodAnalysisContext target,LocalVariable {IsThis:true}]}
                && ProvenDirectBase(owner,target) && !baseSeen)
            {baseSeen=true;baseStoreIndex=stores.Count;baseConstructor=target;continue;}
            if(instruction is not {OpCode:OpCode.Move,
                    Operands:[FieldReference {Parent:null,Local.IsThis:true} field,var value]}
                || !ReferenceEquals(field.Field.DeclaringType,owner) || field.Field.IsStatic
                || field.Offset!=field.Field.Offset || field.Offset<16
                || stores.Any(s=>ReferenceEquals(s.Field,field.Field))
                || Constant(field.Field.FieldType,value,instruction.NativeWriteSize) is not { } constant)return null;
            stores.Add(new(field.Field,constant.Value,instruction.NativeWriteSize,constant.Kind));
        }
        return baseSeen && returned && stores.Count>0 ? new(constructor,stores.ToArray(),baseConstructor,baseStoreIndex) : null;
    }

    private static (long Value,ConstantKind Kind)? Constant(TypeAnalysisContext type,IOperand value,int width)
        => value switch
        {
            Immediate integer when ExactIntegralWidth(type,width)=>(integer.Value,ConstantKind.Integral),
            FloatLiteral single when type.FullName=="System.Single" && width==4
                =>(System.BitConverter.SingleToInt32Bits(single.Value),ConstantKind.Single),
            DoubleLiteral wide when type.FullName=="System.Double" && width==8
                =>(System.BitConverter.DoubleToInt64Bits(wide.Value),ConstantKind.Double),
            _=>null
        };

    private static bool ProvenDirectBase(TypeAnalysisContext owner,MethodAnalysisContext target)
        => target.Name==".ctor" && !target.IsStatic && !target.IsVirtual && target.IsVoid
            && target.Parameters.Count==0 && TrivialConstructorRecovery.SameType(owner.BaseType,target.DeclaringType)
            && (target.DeclaringType?.FullName=="System.Object" ? IsObjectNoOp(target)
                :target.DeclaringType is {GenericParameters.Count:0,IsGenericInstance:false});

    private static bool ExactIntegralWidth(TypeAnalysisContext type,int width)
    {
        var scalar=type.IsEnumType ? type.EnumUnderlyingType : type;
        return width>0 && (scalar?.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32"=>4,
            "System.Int64" or "System.UInt64"=>8,
            _=>0
        })==width;
    }

    private static bool IsObjectNoOp(MethodAnalysisContext target)=>target.Name==".ctor" && !target.IsStatic
        && target.IsVoid && target.Parameters.Count==0 && target.DeclaringType?.FullName=="System.Object"
        && target.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey) is {IsNoOp:true};

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not { } cfg)return 0;
        var count=RecoverBaseInitializer(method);
        foreach(var allocation in cfg.Instructions)
        {
            if(allocation is not {OpCode:OpCode.Newobj,Operands:[LocalVariable obj,TypeAnalysisContext type]}
                || type.GetExtraData<Template[]>(CacheKey) is not {Length:1} templates)continue;
            var template=templates[0];
            if(!ReferenceEquals(template.Constructor.DeclaringType,type))continue;
            var baseStoreIndex=template.BaseStoreIndex<0?template.Stores.Count:template.BaseStoreIndex;
            if(baseStoreIndex>template.Stores.Count)continue;
            var block=cfg.Blocks.Single(b=>b.Instructions.Contains(allocation));
            var at=block.Instructions.IndexOf(allocation)+1;var visited=new HashSet<Block>();
            var aliases=new HashSet<LocalVariable>{obj};var matched=new List<Instruction>();
            var failed=false;var complete=false;Instruction? baseCall=null;
            while(visited.Add(block) && !failed && !complete)
            {
                foreach(var instruction in block.Instructions.Skip(at))
                {
                    if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
                    if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]} && aliases.Contains(source))
                    {aliases.Add(alias);continue;}
                    if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                            Operands:[MethodAnalysisContext target,LocalVariable receiver]}
                        && aliases.Contains(receiver)
                        && (template.BaseConstructor!=null?ReferenceEquals(target,template.BaseConstructor):IsObjectNoOp(target))
                        && baseCall==null && matched.Count==baseStoreIndex)
                    {
                        baseCall=instruction;
                        if(matched.Count==template.Stores.Count){complete=true;break;}
                        continue;
                    }
                    if(matched.Count==baseStoreIndex && baseCall==null
                        || matched.Count>=template.Stores.Count || instruction is not {OpCode:OpCode.Move,
                            Operands:[FieldReference {Parent:null} field,var value]}
                        || !aliases.Contains(field.Local)) {failed=true;break;}
                    var expected=template.Stores[matched.Count];
                    if(!ReferenceEquals(field.Field,expected.Field)
                        || Constant(field.Field.FieldType,value,instruction.NativeWriteSize) is not { } constant
                        || constant.Value!=expected.Value || constant.Kind!=expected.Kind
                        || field.Offset!=expected.Field.Offset
                        || instruction.NativeWriteSize!=expected.Width){failed=true;break;}
                    matched.Add(instruction);
                    if(baseCall!=null && matched.Count==template.Stores.Count){complete=true;break;}
                }
                if(complete || failed || block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)break;
                block=block.Successors[0];at=0;
            }
            // No prefix mutation on a mismatching post-base write/callback.
            // Replacing the exact base call with the original own constructor
            // preserves its before/between/after-store ordering internally.
            if(complete && baseCall!=null)
            {
                baseCall.SetOperand(0,template.Constructor);
                foreach(var store in matched){store.OpCode=OpCode.Nop;store.SetOperands();}
                count++;
            }
        }
        return count;
    }

    // A native compiler can inline the immediate parent's field initializers
    // and leave only its call to the grandparent. Such a call cannot be emitted
    // as a legal C# base initializer. Reuse the COMPLETE original parent template,
    // consuming all its stores in exact order around that exact ancestor call.
    // No name-based deletion/retargeting or partially matched prefix is allowed.
    internal static int RecoverBaseInitializer(MethodAnalysisContext method)
    {
        if(method.Name!=".ctor" || method.IsStatic || !method.IsVoid
            || method.DeclaringType is not {IsValueType:false,GenericParameters.Count:0} owner
            || owner is GenericInstanceTypeAnalysisContext || owner.BaseType is not { } parent
            || parent.GetExtraData<Template[]>(CacheKey) is not {Length:1} templates
            || method.ControlFlowGraph is not { } cfg)return 0;
        var template=templates[0];
        var selfParameters=method.ParameterLocals.Where(p=>p.IsThis).ToArray();
        if(selfParameters.Length!=1 || !TrivialConstructorRecovery.SameType(selfParameters[0].Type,owner)
            || !ReferenceEquals(template.Constructor.DeclaringType,parent) || template.Constructor.Parameters.Count!=0
            || template.BaseConstructor is not { } ancestor || !ProvenDirectBase(parent,ancestor)
            || template.Stores.Count==0 || template.BaseStoreIndex<0
            || template.BaseStoreIndex>template.Stores.Count)return 0;
        var self=selfParameters[0];
        if(cfg.Blocks.SelectMany(b=>b.Instructions).Any(i=>ReferenceEquals(i.Destination,self)
            || i.ImplicitDefinition is { } clobbered && clobbered.Number==self.Register.Number
                && clobbered.Name==self.Register.Name))return 0;
        var initializerCalls=cfg.Instructions.Where(i=>i.IsCall && i.Operands.Count>1
            && i.Operands[0] is MethodAnalysisContext {Name:".ctor"}
            && i.Operands.Count>(i.OpCode==OpCode.Call?2:1)
            && ReferenceEquals(i.Operands[i.OpCode==OpCode.Call?2:1],self)).ToArray();
        if(initializerCalls.Length!=1 || initializerCalls[0] is not
            {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,Operands:[MethodAnalysisContext called,LocalVariable receiver]}
            || !ReferenceEquals(called,ancestor) || !ReferenceEquals(receiver,self))return 0;
        var call=initializerCalls[0];
        var prefix=new List<Instruction>();var seen=new HashSet<Block>();var block=cfg.EntryBlock;
        while(seen.Add(block))
        {
            if(!ReferenceEquals(block,cfg.EntryBlock) && block.Predecessors.Count!=1)break;
            prefix.AddRange(block.Instructions.Where(i=>i.OpCode is not (OpCode.Nop or OpCode.Jump)));
            if(prefix.Count>256 || block.Successors.Count!=1)break;
            block=block.Successors[0];
        }
        if(prefix.Count>256)return 0;
        var start=prefix.IndexOf(call)-template.BaseStoreIndex;
        if(start<0 || start+template.Stores.Count+1>prefix.Count)return 0;
        // A duplicate/unmatched inherited initializer before the selected
        // window is not evidence for a complete parent substitution. Only the
        // child's own field initializers may precede this exact parent segment.
        // FieldReference is a constant *descriptor* in Instruction.Destination;
        // inspect the Move's actual left operand rather than dropping a store.
        if(prefix.Take(start).Any(i=>i is {OpCode:OpCode.Move,Operands:[MemoryOperand,..]}
            || i is {OpCode:OpCode.Move,Operands:[FieldReference field,..]} && (!ReferenceEquals(field.Local,self)
                || field.Parent!=null || !ReferenceEquals(field.Field.DeclaringType,owner))))return 0;
        var matched=new List<Instruction>();var storeIndex=0;
        for(var index=0;index<template.Stores.Count+1;index++)
        {
            var instruction=prefix[start+index];
            if(index==template.BaseStoreIndex)
            {if(!ReferenceEquals(instruction,call))return 0;continue;}
            var expected=template.Stores[storeIndex++];
            if(instruction is not {OpCode:OpCode.Move,Operands:[FieldReference {Parent:null} field,var value]}
                || !ReferenceEquals(field.Local,self) || !ReferenceEquals(field.Field,expected.Field)
                || field.Offset!=expected.Field.Offset || instruction.NativeWriteSize!=expected.Width
                || Constant(field.Field.FieldType,value,instruction.NativeWriteSize) is not { } constant
                || constant.Value!=expected.Value || constant.Kind!=expected.Kind)return 0;
            matched.Add(instruction);
        }
        call.SetOperand(0,template.Constructor);
        foreach(var store in matched){store.OpCode=OpCode.Nop;store.SetOperands();}
        return 1;
    }
}
