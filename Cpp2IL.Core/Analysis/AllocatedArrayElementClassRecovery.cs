using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// An actual unique newarr proves its runtime element class. An array parameter
// or field with the same static type does NOT: covariance must stay dynamic.
// The original helper/IsInst mapping is already reviewed (runtime-array-checks
// round61); this pass adds allocation provenance, never removes a guard/throw.
public static class AllocatedArrayElementClassRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph || graph.Blocks.Count>512
            || graph.Instructions.Count()>16384 || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        var changed=0;
        foreach(var instruction in graph.Instructions.ToArray())
            if(instruction.NativeDirectCallTarget==0xABB8FC && TryRewrite(method,instruction))changed++;
        return changed;
    }

    internal static bool TryRewrite(MethodAnalysisContext method,Instruction call)
    {
        if(method.ControlFlowGraph is not {} graph || call.NativeDirectCallTarget!=0xABB8FC || call is not {OpCode:OpCode.Call,
            Operands:[StringLiteral {Value:"il2cpp_vm_object_is_inst"},LocalVariable result,var value,LocalVariable handle,..]}
            || result.Type is {IsValueType:true} or ByRefTypeAnalysisContext || !ReferenceValue(value))return false;
        var all=graph.Instructions.ToArray();
        var definitions=all.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        if(!definitions.TryGetValue(handle,out var elementLoad) || elementLoad is not
            {OpCode:OpCode.Move,NativeReadSize:8,Operands:[_,MemoryOperand {Base:LocalVariable klass,Addend:0x40,Index:null}]}
            || !definitions.TryGetValue(klass,out var classLoad) || classLoad is not
            {OpCode:OpCode.Move,NativeReadSize:8,Operands:[_,MemoryOperand {Base:LocalVariable array,Addend:0,Index:null}]}
            || !definitions.TryGetValue(array,out var allocation) || allocation is not
            {OpCode:OpCode.NewArr,Operands:[_,SzArrayTypeAnalysisContext allocatedType,_]}
            || array.Type is not SzArrayTypeAnalysisContext declaredType
            || !ReferenceEquals(allocatedType.ElementType,declaredType.ElementType))return false;
        var element=allocatedType.ElementType;
        if(element.IsValueType || element is ByRefTypeAnalysisContext || element.HasAnyGenericParameters()
            || element is not GenericInstanceTypeAnalysisContext && element.GenericParameters.Count!=0
            || klass.Type!=null && (klass.Type is not RuntimeClassTypeAnalysisContext classType
                || classType.RepresentedType is not SzArrayTypeAnalysisContext classArray
                || !ReferenceEquals(classArray.ElementType,element))
            || handle.Type!=null && (handle.Type is not RuntimeClassTypeAnalysisContext elementClass
                || !ReferenceEquals(elementClass.RepresentedType,element)))return false;
        if(!ForwardNullCheckRecovery.DefinitionDominates(graph,allocation,classLoad)
            || !ForwardNullCheckRecovery.DefinitionDominates(graph,classLoad,elementLoad)
            || !ForwardNullCheckRecovery.DefinitionDominates(graph,elementLoad,call)
            || new[]{array,klass,handle}.Any(local=>all.Any(i=>i.Operands.Any(o=>Escapes(o,local)))))return false;

        // Only after every identity, definition, width and dominance proof.
        // Preserve the nullable result and every existing branch/exception.
        call.OpCode=OpCode.IsInst;call.SetOperands(result,element,value);
        result.Type??=element;
        return true;
    }

    private static bool ReferenceValue(IOperand value)=>value switch
    {
        StringLiteral=>true,
        Immediate {Value:0}=>true,
        LocalVariable {Type:{} type}=>!type.IsValueType && type is not
            (ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext),
        FieldReference {Field.FieldType:{} type}=>!type.IsValueType && type is not ByRefTypeAnalysisContext,
        _=>false,
    };

    private static bool Escapes(IOperand operand,LocalVariable local)=>operand switch
    {
        AddressOf address=>ForwardNullCheckRecovery.Uses(address.Target,local),
        MemoryOperand memory=>memory.Base!=null && Escapes(memory.Base,local) || memory.Index!=null && Escapes(memory.Index,local),
        ArrayAccess access=>Escapes(access.Array,local) || Escapes(access.Index,local),
        ArrayLength length=>Escapes(length.Array,local),
        FieldReference field=>field.Parent!=null && Escapes(field.Parent,local),
        _=>false,
    };
}
