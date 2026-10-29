using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// The call's actual MethodInfo provides the definition/type arguments. Native
// equivalence is only a second, independent witness; never use a name/shape as
// the method identity and never add inferred entries to MethodsByAddress.
internal static class NativeReceiverCounterpartRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Dictionary<ulong,int>?>> Ranges=new();

    private static MethodAnalysisContext Base(MethodAnalysisContext m)
        => m is ConcreteGenericMethodAnalysisContext c?c.BaseMethodContext:m;
    private static FieldAnalysisContext BaseField(FieldAnalysisContext f)
        => f is ConcreteGenericFieldAnalysisContext c?c.BaseFieldContext:f;

    internal static bool SameStorage(TypeAnalysisContext a,TypeAnalysisContext b,int depth=0)
    {
        if(depth>=16 || a.HasAnyGenericParameters() || b.HasAnyGenericParameters()
            || a is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
            || b is PointerTypeAnalysisContext or ByRefTypeAnalysisContext)return false;
        if(a.IsValueType!=b.IsValueType)return false;
        if(!a.IsValueType)return true;
        if(TrivialConstructorRecovery.SameType(a,b))return true;
        if(a is not GenericInstanceTypeAnalysisContext x || b is not GenericInstanceTypeAnalysisContext y
            || !ReferenceEquals(x.GenericType,y.GenericType))return false;
        return SameFields(ClosedGenericValueLayout.Fields(a,8),ClosedGenericValueLayout.Fields(b,8),depth+1);
    }

    private static bool SameFields(IReadOnlyList<ClosedGenericValueLayout.FieldStorage>? left,
        IReadOnlyList<ClosedGenericValueLayout.FieldStorage>? right,int depth=0)
    {
        if(left==null || right==null || left.Count!=right.Count || left.Count==0)return false;
        for(var i=0;i<left.Count;i++)
            if(left[i].Offset!=right[i].Offset || left[i].Size!=right[i].Size
                || !ReferenceEquals(BaseField(left[i].Field),BaseField(right[i].Field))
                || !SameStorage(left[i].Field.FieldType,right[i].Field.FieldType,depth+1))return false;
        return true;
    }

    internal static bool ManagedWitness(MethodAnalysisContext target,MethodAnalysisContext witness,
        MethodAnalysisContext? caller=null)
    {
        if(!ReferenceEquals(Base(target),Base(witness)) || target is not ConcreteGenericMethodAnalysisContext concrete
            || target.IsStatic || !target.IsVoid || target.Name!=".ctor" || target.GenericParameters.Count!=0
            || concrete.MethodGenericParameters.Count!=0 || target.DeclaringType?.IsValueType!=true
            || witness is not ConcreteGenericMethodAnalysisContext {MethodRef:not null} registered
            || !target.AppContext.ConcreteGenericMethodsByRef.TryGetValue(registered.MethodRef,out var live)
            || !ReferenceEquals(live,witness) || witness.IsStatic || !witness.IsVoid
            || target.Parameters.Count!=witness.Parameters.Count)return false;
        if(!target.DeclaringType.HasAnyGenericParameters())
        {
            if(!SameStorage(target.DeclaringType,witness.DeclaringType!))return false;
            return target.Parameters.Zip(witness.Parameters,(a,b)=>SameStorage(a.ParameterType,b.ParameterType)).All(x=>x);
        }
        // An open return is authorized by EVERY actual closed alias of this
        // exact caller. All aliases must expose the same closed field layout;
        // unknown T is never globally changed to object/reference storage.
        if(caller==null || caller is ConcreteGenericMethodAnalysisContext || caller.IsStatic
            || caller.Parameters.Count!=0 || target.Parameters.Count!=1
            || !TrivialConstructorRecovery.SameType(target.DeclaringType,caller.ReturnType)
            || caller.DeclaringType is not {} owner
            || !TrivialConstructorRecovery.SameType(target.Parameters[0].ParameterType,
                owner.GenericParameters.Count==0?owner:owner.MakeGenericInstanceType(owner.GenericParameters))
            || SharedGenericReturnLayout.TryGet(caller)is not {} scoped)return false;
        var witnessFields=ClosedGenericValueLayout.Fields(witness.DeclaringType!,8);
        var aliases=caller.AppContext.MethodsByAddress[caller.UnderlyingPointer];
        foreach(var alias in aliases)
        {
            if(ReferenceEquals(alias,caller))continue;
            if(!SameFields(ClosedGenericValueLayout.Fields(alias.ReturnType,8),witnessFields)
                || !SameStorage(alias.DeclaringType!,witness.Parameters[0].ParameterType))return false;
        }
        return scoped.ConcreteAliases==aliases.Count-1;
    }

    internal static bool Matches(MethodAnalysisContext target,ulong entry,MethodAnalysisContext? caller=null)
    {
        if(entry==0 || entry%4!=0 || !CheckedUnboxRecovery.Supports(target.AppContext))return false;
        var app=target.AppContext;
        var ranges=Ranges.GetValue(app,a=>new Lazy<Dictionary<ulong,int>?>(()=>NativeReceiverUnwindRanges.ForImage(a))).Value;
        if(ranges==null || !ranges.TryGetValue(entry,out var length) || length is <8 or >4096)return false;
        foreach(var witness in RegisteredMethodIdentityIndex.Candidates(target))
        {
            if(!ManagedWitness(target,witness,caller) || witness.UnderlyingPointer==entry
                || !ranges.TryGetValue(witness.UnderlyingPointer,out var otherLength) || length!=otherLength)continue;
            if(!app.Binary.TryMapVirtualAddressToRaw(entry,out var a)
                || !app.Binary.TryMapVirtualAddressToRaw(witness.UnderlyingPointer,out var b)
                || a<0 || b<0 || a>app.Binary.RawLength-length || b>app.Binary.RawLength-length)continue;
            var bytes=app.Binary.GetRawBinaryContent();
            if(NativeReceiverCounterpartProof.Equivalent(bytes.Slice((int)b,length),witness.UnderlyingPointer,
                bytes.Slice((int)a,length),entry,true))return true;
        }
        return false;
    }

    internal static bool TryResolve(MethodAnalysisContext caller,Instruction call)
    {
        var first=call.OpCode==OpCode.Call?2:1;
        if(!call.IsCall || call.NativeVirtualDispatch || call.Operands[0]is not Immediate address)return false;
        // Constructors return void, so the actual native argument list is
        // receiver, declared parameters, hidden MethodInfo -- no hidden X8.
        for(var count=0;count<=8;count++)
        {
            var infoAt=first+1+count;
            if(infoAt>=call.Operands.Count)break;
            var info=call.Operands[infoAt]switch {
                RuntimeMethodInfoAnalysisContext m=>m,
                LocalVariable {Type:RuntimeMethodInfoAnalysisContext m}=>m,_=>null};
            if(info?.RepresentedMethod is not {Name:".ctor",IsStatic:false,IsVoid:true} target
                || target.Parameters.Count!=count || !Matches(target,address.UnsignedValue,caller))continue;
            // Multiple metadata-bearing argument positions are ambiguous.
            if(call.Operands.Where((_,i)=>i!=infoAt).Any(o=>o is RuntimeMethodInfoAnalysisContext
                or LocalVariable {Type:RuntimeMethodInfoAnalysisContext}))return false;
            call.SetOperand(0,target);
            target.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(call,target);
            return true;
        }
        return false;
    }
}
