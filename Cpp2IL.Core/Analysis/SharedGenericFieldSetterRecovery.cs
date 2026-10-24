using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// All known closed bodies must store the ONE declared argument into the SAME
// original field. Registers are checked per closed ABI, never guessed from T.
public static class SharedGenericFieldSetterRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Dictionary<MethodAnalysisContext,ConcreteGenericMethodAnalysisContext[]>> Aliases=new();
    private static FieldAnalysisContext Base(FieldAnalysisContext field)=>field is ConcreteGenericFieldAnalysisContext c?Base(c.BaseFieldContext):field;

    public static bool Run(MethodAnalysisContext method)
    {
        if(method.IsStatic || method.Definition==null || method is ConcreteGenericMethodAnalysisContext
            || method.DeclaringType is not {IsValueType:false} owner || method.ReturnType.FullName!="System.Void"
            || method.Parameters.Count!=1 || method.GenericParameters.Count!=0
            || method.Parameters[0].ParameterType is not GenericParameterTypeAnalysisContext {Type:Il2CppTypeEnum.IL2CPP_TYPE_VAR} parameter
            || !ReferenceEquals(parameter.Owner,owner) || method.ControlFlowGraph==null)return false;
        var proofs=NativeFieldStoreProofs.For(method.AppContext);if(proofs.Count==0)return false;
        var aliases=Aliases.GetValue(method.AppContext,app=>app.MethodsByAddress.Values.SelectMany(v=>v)
            .OfType<ConcreteGenericMethodAnalysisContext>().Distinct().GroupBy(m=>m.BaseMethodContext)
            .ToDictionary(g=>g.Key,g=>g.ToArray()));
        if(!aliases.TryGetValue(method,out var closed) || closed.Length==0)return false;
        var field=Prove(owner,parameter,closed,v=>proofs.TryGetValue(v.UnderlyingPointer,out var p)?p.Stores:null,f=>f.BackingData!=null);
        var receivers=method.ParameterLocals.Where(v=>v.IsThis && SharedGenericFieldGetterRecovery.IsOpenSelf(v.Type,owner)).ToArray();
        if(field==null || receivers.Length!=1 || method.Parameters[0].ParameterIndex!=0)return false;
        var value=new LocalVariable("generic_field_value",new(null,"generic_field_value"),parameter){ParameterIndex=0};
        var accessed=receivers[0].Type is GenericInstanceTypeAnalysisContext self?new ConcreteGenericFieldAnalysisContext(field,self):field;
        method.ParameterLocals=[receivers[0],value];
        method.ControlFlowGraph=new ISILControlFlowGraph([
            new(0,OpCode.Move,new FieldReference(accessed,receivers[0],0),value),new(1,OpCode.Return)]);
        return true;
    }

    internal static FieldAnalysisContext? Prove(TypeAnalysisContext owner,GenericParameterTypeAnalysisContext parameter,
        IReadOnlyList<ConcreteGenericMethodAnalysisContext> closed,
        Func<ConcreteGenericMethodAnalysisContext,IReadOnlyList<NativeFieldLoadProofs.Read>?> storesFor,
        Func<FieldAnalysisContext,bool> originalField)
    {
        if(closed.Count==0 || owner.IsValueType || parameter.Type!=Il2CppTypeEnum.IL2CPP_TYPE_VAR
            || !ReferenceEquals(parameter.Owner,owner) || closed.Any(v=>!ReferenceEquals(v.BaseMethodContext.DeclaringType,owner)
                || v.BaseMethodContext.IsStatic || v.BaseMethodContext.Parameters.Count!=1
                || v.BaseMethodContext.GenericParameters.Count!=0 || v.BaseMethodContext.ReturnType.FullName!="System.Void"
                || !ReferenceEquals(v.BaseMethodContext.Parameters[0].ParameterType,parameter)))return null;
        var candidates=owner.Fields.Where(f=>!f.IsStatic && (f.Attributes&FieldAttributes.InitOnly)==0 && originalField(f)
            && f.FieldType is GenericParameterTypeAnalysisContext p && p.Type==parameter.Type && p.Index==parameter.Index
            && ReferenceEquals(p.Owner,owner)).ToArray();
        var proven=new List<FieldAnalysisContext>();
        foreach(var field in candidates)
        {
            var valid=true;
            foreach(var variant in closed)
            {
                if(storesFor(variant) is not {} stores || variant.Parameters.Count!=1
                    || variant.Parameters[0].ParameterType.HasAnyGenericParameters() || variant.DeclaringType==null
                    || GenericInstanceFieldLayout.InheritedFields(variant.DeclaringType) is not {} layout)
                {valid=false;break;}
                var type=variant.Parameters[0].ParameterType;
                var storage=layout.Where(f=>ReferenceEquals(Base(f.Field),field)
                    && NullBypassRuntimeCastRecovery.SameCastType(f.Field.FieldType,type)).ToArray();
                // Class receiver is X0; its sole argument uses X1/X2 or V0..V3.
                if(stores.Any(s=>s.Kind=="gpr" && s.Register is not (1 or 2)) || storage.Length!=1
                    || !SharedGenericFieldGetterRecovery.Matches(type,storage[0].Offset,storage[0].Size,
                        stores.Select(s=>s with {Register=s.Kind=="gpr"?s.Register-1:s.Register}).ToArray()))
                {valid=false;break;}
            }
            if(valid)proven.Add(field);
        }
        return proven.Count==1?proven[0]:null;
    }
}
