using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Reuse independently pinned whole-FDE load effects AND the existing ARM64
// aggregate return/layout matcher. Never infer a Vector/Rect layout by name.
public static class NativeAggregateFieldAccessorRecovery
{
    internal sealed record Contract(MethodAnalysisContext Method,int Size);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<FieldAnalysisContext,Contract>>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph==null || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        var catalog=Catalogs.GetValue(method.AppContext,a=>new Lazy<Dictionary<FieldAnalysisContext,Contract>>(()=>Build(a))).Value;
        return Recover(method,catalog);
    }

    private static Dictionary<FieldAnalysisContext,Contract> Build(ApplicationAnalysisContext app)
    {
        var native=NativeFieldLoadProofs.For(app);var candidates=new Dictionary<FieldAnalysisContext,List<Contract>>();
        foreach(var target in app.MethodsByAddress.Values.SelectMany(v=>v).Distinct())
        {
            if(target.UnderlyingPointer==0 || !native.TryGetValue(target.UnderlyingPointer,out var proof)
                || target.DeclaringType is not {IsValueType:false} owner)continue;
            foreach(var field in owner.Fields)
            {
                if(Prove(target,field,proof.Reads) is not {} contract)continue;
                if(!candidates.TryGetValue(field,out var list))candidates[field]=list=[];
                list.Add(contract);
            }
        }
        var result=new Dictionary<FieldAnalysisContext,Contract>();
        foreach(var (field,list) in candidates)
        {
            var ordinary=list.Where(c=>!c.Method.DeclaringType!.Properties.Any(p=>ReferenceEquals(p.Getter,c.Method))).ToArray();
            var choices=ordinary.Length>0?ordinary:list.ToArray();
            if(choices.Length==1)result[field]=choices[0];
        }
        return result;
    }

    internal static Contract? Prove(MethodAnalysisContext target,FieldAnalysisContext field,IReadOnlyList<NativeFieldLoadProofs.Read> reads)
    {
        if(target.IsStatic || target.IsVirtual || target.IsVoid || target.Visibility!=MethodAttributes.Public
            || target.Parameters.Count!=0 || target.GenericParameters.Count!=0 || target.Name.StartsWith(".")
            || target.DeclaringType is not {IsValueType:false} owner || owner.IsGenericInstance || owner.GenericParameters.Count!=0
            || target.ReturnType is not {IsValueType:true} returned || returned.IsEnumType || TypeSizes.IsScalarValueType(returned)
            || returned.HasAnyGenericParameters() || !TrivialConstructorRecovery.SameType(returned,field.FieldType)
            || !ReferenceEquals(field.DeclaringType,owner) || !owner.Fields.Contains(field) || field.IsStatic
            || (field.Attributes&FieldAttributes.Literal)!=0 || field.Offset<16)return null;
        var size=TypeSizes.UnboxedSize(returned,8);
        return size>0 && size<=32 && SharedGenericFieldGetterRecovery.Matches(returned,field.Offset,size,reads)
            ?new(target,(int)size):null;
    }

    private static bool Receiver(LocalVariable local,TypeAnalysisContext owner)
    {
        if(local.Type is not {IsValueType:false} type || type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            || type.Type is not (Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST))return false;
        var seen=new HashSet<TypeAnalysisContext>();
        for(var current=type;current!=null && seen.Add(current) && seen.Count<=32;current=current.BaseType)
            if(TrivialConstructorRecovery.SameType(current,owner))return true;
        return false;
    }

    private static void Call(Instruction instruction,Contract contract,LocalVariable result,LocalVariable receiver)
    {
        instruction.OpCode=OpCode.Call;instruction.SetOperands(contract.Method,result,receiver);
        instruction.NativeReadSize=0;instruction.NativeDirectCallTarget=contract.Method.UnderlyingPointer;
        instruction.NativeNullCheckedCall=true;instruction.NativeVirtualDispatch=false;
    }

    internal static int Recover(MethodAnalysisContext method,IReadOnlyDictionary<FieldAnalysisContext,Contract> catalog)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;var count=0;
        foreach(var block in graph.Blocks)
        for(var index=0;index<block.Instructions.Count;index++)
        {
            var instruction=block.Instructions[index];
            if(instruction is not {OpCode:OpCode.Move,NativeWriteSize:0,Operands:[LocalVariable result,FieldReference field]})continue;
            var root=field.Parent??field;
            if(root.Parent!=null || !catalog.TryGetValue(root.Field,out var contract) || root.Offset!=root.Field.Offset
                || !Receiver(root.Local,root.Field.DeclaringType)
                || TrivialConstructorRecovery.SameType(method.DeclaringType,root.Field.DeclaringType))continue;
            if(field.Parent==null)
            {
                if(instruction.NativeReadSize!=contract.Size)continue;
                Call(instruction,contract,result,root.Local);block.CalculateBlockType();count++;continue;
            }
            // Read-only component extraction from a proven inline value. Do not
            // turn storage/ref/out or arbitrary partial reads into value copies.
            if(!ReferenceEquals(field.Local,root.Local) || !root.Field.FieldType.IsValueType || instruction.NativeReadSize<=0
                || TypeSizes.UnboxedSize(field.Field.FieldType,8)!=instruction.NativeReadSize)continue;
            var temporary=new LocalVariable("public_aggregate_"+serial,new Register(null,"PUBLIC_AGGREGATE_"+serial),root.Field.FieldType);
            var replacement=NestedFieldAccess.Find(root.Field.FieldType,temporary,field.Offset,instruction.NativeReadSize,method);
            if(replacement==null || !ReferenceEquals(replacement.Field,field.Field))continue;
            var call=new Instruction(serial++,OpCode.Nop);Call(call,contract,temporary,root.Local);
            method.Locals.Add(temporary);block.Instructions.Insert(index,call);index++;
            instruction.SetOperand(1,replacement);block.CalculateBlockType();count++;
        }
        return count;
    }
}
