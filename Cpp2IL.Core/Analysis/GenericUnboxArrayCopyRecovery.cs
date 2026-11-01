using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Keep ALL existing null/bounds branches in their original positions. Only
// replace the reviewed helper and its complete nonescaping payload copy.
public static class GenericUnboxArrayCopyRecovery
{
    const ulong Helper=0xA61E70;
    public static bool Run(MethodAnalysisContext method)
    {
        if(!method.ControlFlowGraph!.Instructions.Any(i=>i is {OpCode:OpCode.Call,
            Operands:[Immediate {UnsignedValue:Helper},..]}) || !CheckedUnboxRecovery.Supports(method.AppContext))return false;
        return Rewrite(method,p=>ProveSize(method,p));
    }

    static int? ProveSize(MethodAnalysisContext method,GenericParameterTypeAnalysisContext parameter)
    {
        if(parameter.Type!=Il2CppTypeEnum.IL2CPP_TYPE_VAR || !ReferenceEquals(parameter.Owner,method.DeclaringType)
            || !method.AppContext.MethodsByAddress.TryGetValue(method.UnderlyingPointer,out var variants))return null;
        var closed=variants.OfType<ConcreteGenericMethodAnalysisContext>().Where(m=>ReferenceEquals(m.BaseMethodContext,method)).ToArray();
        if(closed.Length==0 || variants.Any(m=>!ReferenceEquals(m,method)
            && (m is not ConcreteGenericMethodAnalysisContext c || !ReferenceEquals(c.BaseMethodContext,method))))return null;
        int? size=null;
        foreach(var variant in closed)
        {
            if(parameter.Index>=variant.TypeGenericParameters.Count)return null;
            var type=variant.TypeGenericParameters[parameter.Index];
            if(!type.IsValueType || type.HasAnyGenericParameters()
                || type is GenericInstanceTypeAnalysisContext {GenericType.FullName:"System.Nullable`1"})return null;
            var width=TypeSizes.UnboxedSize(type,method.AppContext.Binary.PointerSizeBytes);
            if(width is <=0 or >64 || size!=null && size!=width)return null;
            size=(int)width;
        }
        return size;
    }

    internal static bool Rewrite(MethodAnalysisContext method,Func<GenericParameterTypeAnalysisContext,int?> proveSize)
    {
        var graph=method.ControlFlowGraph!;var instructions=graph.Instructions.ToArray();
        if(!method.IsVoid || method.IsStatic || instructions.Any(i=>i.OpCode==OpCode.Return && i.Operands.Count!=0))return false;
        var calls=instructions.Where(i=>i.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall).ToArray();
        if(calls.Length!=1 || calls[0] is not {OpCode:OpCode.Call,Operands:[Immediate {UnsignedValue:Helper},
            LocalVariable pointer,LocalVariable {Type.FullName:"System.Object"} value,RuntimeClassTypeAnalysisContext handle,..]} call
            || handle.RepresentedType is not GenericParameterTypeAnalysisContext parameter
            || pointer.Type!=null || pointer.IsThis || ReferenceEquals(pointer,value)
            || method.ParameterLocals?.Contains(pointer)==true)return false;
        var loads=instructions.Where(i=>i is {OpCode:OpCode.Move,Operands:[LocalVariable,
            MemoryOperand {Index:null,Scale:0} memory]} && ReferenceEquals(memory.Base,pointer)).ToArray();
        if(loads.Length==0 || loads.Select(i=>i.Operands[0]).Distinct().Count()!=loads.Length)return false;
        var chunks=loads.ToDictionary(i=>(LocalVariable)i.Operands[0]);
        var stores=instructions.Where(i=>i is {OpCode:OpCode.Move,Operands:[_,LocalVariable chunk]} && chunks.ContainsKey(chunk)).ToArray();
        var typed=stores.Where(i=>i.Operands[0] is ArrayAccess).ToArray();
        if(stores.Length!=loads.Length || typed.Length!=1
            || typed[0].Operands[0] is not ArrayAccess {Index:Immediate {Value:0}} target
            || target.Array.Type is not SzArrayTypeAnalysisContext {ElementType:GenericParameterTypeAnalysisContext element}
            || !ReferenceEquals(element,parameter))return false;
        var size=proveSize(parameter);if(size is not >0 or >64)return false;
        var homes=graph.Blocks.Where(b=>stores.Any(b.Instructions.Contains)).ToArray();
        if(homes.Length!=1 || !ReferenceEquals(homes[0].Instructions.First(i=>stores.Contains(i)),typed[0]))return false;
        var covered=new HashSet<int>();
        foreach(var store in stores)
        {
            var load=chunks[(LocalVariable)store.Operands[1]];var memory=(MemoryOperand)load.Operands[1];
            var width=load.NativeReadSize;
            if(width is not (1 or 2 or 4 or 8 or 16) || store.NativeWriteSize!=width || memory.Addend<0
                || memory.Addend+width>size || !ForwardNullCheckRecovery.DefinitionDominates(graph,call,load)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph,load,typed[0]))return false;
            var offset=ReferenceEquals(store,typed[0])?0:
                store.Operands[0] is MemoryOperand {Index:null,Scale:0} dest && ReferenceEquals(dest.Base,target.Array)?dest.Addend-32:-1;
            if(offset!=memory.Addend)return false;
            for(var b=(int)offset;b<offset+width;b++)if(!covered.Add(b))return false;
        }
        if(covered.Count!=size)return false;
        foreach(var instruction in instructions)
        {
            if(ReferenceEquals(instruction,call)||loads.Contains(instruction)||stores.Contains(instruction))continue;
            if(instruction.Operands.Any(o=>ForwardNullCheckRecovery.Uses(o,pointer)
                || chunks.Keys.Any(c=>ForwardNullCheckRecovery.Uses(o,c))))return false;
            if(instruction.Destination is FieldReference or MemoryOperand or ArrayAccess)return false;
            if(instruction.OpCode==OpCode.Newobj && instruction.Operands is not
                [_,TypeAnalysisContext {FullName:"System.IndexOutOfRangeException" or "System.NullReferenceException"}])return false;
        }
        // Conversion stays at the helper, array/bounds/null operations stay
        // exactly where they were. No helper is swallowed into a later store.
        call.OpCode=OpCode.UnboxAny;call.SetOperands(pointer,parameter,value);pointer.Type=parameter;
        foreach(var instruction in loads.Concat(stores))
        {instruction.OpCode=OpCode.Nop;instruction.SetOperands();instruction.NativeReadSize=instruction.NativeWriteSize=0;}
        typed[0].OpCode=OpCode.Move;typed[0].SetOperands(target,pointer);
        return true;
    }
}
