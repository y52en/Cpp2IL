using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// A closed T may return in SIMD registers while the open definition guesses X0.
// Recover the type-independent field read only if ALL known concrete entries
// are complete original load/RET functions reading that SAME metadata field.
public static class SharedGenericFieldGetterRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Dictionary<MethodAnalysisContext,ConcreteGenericMethodAnalysisContext[]>> Aliases=new();
    private static FieldAnalysisContext Base(FieldAnalysisContext field)=>field is ConcreteGenericFieldAnalysisContext c?Base(c.BaseFieldContext):field;

    public static bool Run(MethodAnalysisContext method)
    {
        if(method.IsStatic || method.Definition==null || method.DeclaringType is not {IsValueType:false} owner
            || method is ConcreteGenericMethodAnalysisContext
            || method.ReturnType is not GenericParameterTypeAnalysisContext {Type:Il2CppTypeEnum.IL2CPP_TYPE_VAR} parameter
            || !ReferenceEquals(parameter.Owner,owner) || method.ControlFlowGraph==null)return false;
        var proofs=NativeFieldLoadProofs.For(method.AppContext);if(proofs.Count==0)return false;
        var variants=Aliases.GetValue(method.AppContext,app=>app.MethodsByAddress.Values.SelectMany(v=>v)
            .OfType<ConcreteGenericMethodAnalysisContext>().Distinct().GroupBy(m=>m.BaseMethodContext)
            .ToDictionary(g=>g.Key,g=>g.ToArray()));
        if(!variants.TryGetValue(method,out var closed) || closed.Length==0)return false;
        var field=Prove(owner,parameter,closed,v=>proofs.TryGetValue(v.UnderlyingPointer,out var p)?p.Reads:null,
            f=>f.BackingData!=null);
        var receivers=method.ParameterLocals.Where(v=>v.IsThis && IsOpenSelf(v.Type,owner)).ToArray();
        if(field==null || receivers.Length!=1)return false;
        var result=new LocalVariable("generic_field_result",new(null,"generic_field_result"),parameter);
        var accessed=receivers[0].Type is GenericInstanceTypeAnalysisContext self
            ?new ConcreteGenericFieldAnalysisContext(field,self):field;
        method.ControlFlowGraph=new ISILControlFlowGraph([
            new(0,OpCode.Move,result,new FieldReference(accessed,receivers[0],0)),new(1,OpCode.Return,result)]);
        return true;
    }

    internal static bool IsOpenSelf(TypeAnalysisContext? type,TypeAnalysisContext owner)
        =>ReferenceEquals(type,owner) || type is GenericInstanceTypeAnalysisContext generic
            && ReferenceEquals(generic.GenericType,owner) && generic.GenericArguments.Count==owner.GenericParameters.Count
            && generic.GenericArguments.Select((argument,index)=>ReferenceEquals(argument,owner.GenericParameters[index])).All(equal=>equal);

    internal static FieldAnalysisContext? Prove(TypeAnalysisContext owner,GenericParameterTypeAnalysisContext parameter,
        IReadOnlyList<ConcreteGenericMethodAnalysisContext> closed,
        Func<ConcreteGenericMethodAnalysisContext,IReadOnlyList<NativeFieldLoadProofs.Read>?> readsFor,
        Func<FieldAnalysisContext,bool> originalField)
    {
        if(closed.Count==0 || owner.IsValueType || parameter.Type!=Il2CppTypeEnum.IL2CPP_TYPE_VAR
            || !ReferenceEquals(parameter.Owner,owner)
            || closed.Any(v=>!ReferenceEquals(v.BaseMethodContext.DeclaringType,owner)
                || !ReferenceEquals(v.BaseMethodContext.ReturnType,parameter)))return null;
        var candidates=owner.Fields.Where(f=>!f.IsStatic && originalField(f)
            && f.FieldType is GenericParameterTypeAnalysisContext p && p.Type==parameter.Type
            && p.Index==parameter.Index && ReferenceEquals(p.Owner,owner)).ToArray();
        var proven=new List<FieldAnalysisContext>();
        foreach(var field in candidates)
        {
            var valid=true;
            foreach(var variant in closed)
            {
                if(readsFor(variant) is not {} reads
                    || variant.ReturnType.HasAnyGenericParameters() || variant.DeclaringType==null
                    || GenericInstanceFieldLayout.InheritedFields(variant.DeclaringType) is not {} layout)
                {valid=false;break;}
                var storage=layout.Where(f=>ReferenceEquals(Base(f.Field),field)
                    && NullBypassRuntimeCastRecovery.SameCastType(f.Field.FieldType,variant.ReturnType)).ToArray();
                if(storage.Length!=1 || !Matches(variant.ReturnType,storage[0].Offset,storage[0].Size,reads))
                {valid=false;break;}
            }
            if(valid)proven.Add(field);
        }
        return proven.Count==1?proven[0]:null;
    }

    internal static bool Matches(TypeAnalysisContext type,long offset,long size,IReadOnlyList<NativeFieldLoadProofs.Read> reads)
    {
        if(reads.Count==0 || reads.Select(r=>(r.Kind,r.Register)).Distinct().Count()!=reads.Count)return false;
        if(type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext
            || type.HasAnyGenericParameters())return false;
        var hfa=Arm64HfaLayout.Fields(type);
        if(type.FullName is "System.Single" or "System.Double")
        {
            var scalarWidth=type.FullName=="System.Single"?4:8;
            return size==scalarWidth && reads.Count==1 && reads[0] is {Kind:"fp",Register:0}
                && reads[0].Width==scalarWidth && reads[0].Offset==offset;
        }
        if(hfa!=null)
            return reads.Count==hfa.Length && size==TypeSizes.UnboxedSize(type,8)
                && hfa.Select((lane,index)=>reads.SingleOrDefault(r=>r.Kind=="fp" && r.Register==index) is {} read
                    && read.Width==(lane.FieldType.FullName=="System.Single"?4:8) && read.Offset==offset+lane.Offset).All(v=>v);
        if(size is not (1 or 2 or 4 or 8 or 16) || (type.IsValueType?TypeSizes.UnboxedSize(type,8):8)!=size)return false;
        var count=size==16?2:1;var width=size==16?8:(int)size;
        return reads.Count==count && Enumerable.Range(0,count).All(index=>reads.SingleOrDefault(r=>r.Kind=="gpr" && r.Register==index) is {} read
            && read.Width==width && read.Offset==offset+index*width);
    }
}
