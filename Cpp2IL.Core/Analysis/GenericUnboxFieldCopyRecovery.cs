using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Reassemble only a complete value copy from the reviewed checked-unbox helper.
// Native FieldReference.Offset AND every concrete native variant's metadata
// layout must agree. Open generic sizes, partial copies and escaping pointers
// remain diagnostics; this never turns a proposal into a native certificate.
public static class GenericUnboxFieldCopyRecovery
{
    const ulong Target=0xA61E70;
    static FieldAnalysisContext Definition(FieldAnalysisContext field)
        => field is ConcreteGenericFieldAnalysisContext concrete ? Definition(concrete.BaseFieldContext) : field;
    public static bool Run(MethodAnalysisContext method)
    {
        if (!method.ControlFlowGraph!.Instructions.Any(i=>i is {OpCode:OpCode.Call,
                Operands:[Immediate {UnsignedValue:Target},..]})
            || !CheckedUnboxRecovery.Supports(method.AppContext)) return false;
        return Rewrite(method,(parameter,field)=>ProveLayout(method,parameter,field));
    }

    static int? ProveLayout(MethodAnalysisContext method,GenericParameterTypeAnalysisContext parameter,FieldReference field)
    {
        if (parameter.Type!=Il2CppTypeEnum.IL2CPP_TYPE_VAR || !ReferenceEquals(parameter.Owner,method.DeclaringType)
            || Definition(field.Field).BackingData==null || field.Offset<0 || field.Offset>4096
            || !method.AppContext.MethodsByAddress.TryGetValue(method.UnderlyingPointer,out var variants)) return null;
        var closed=variants.OfType<ConcreteGenericMethodAnalysisContext>()
            .Where(m=>ReferenceEquals(m.BaseMethodContext,method)).ToArray();
        if (closed.Length==0 || variants.Any(m=>!ReferenceEquals(m,method)
            && (m is not ConcreteGenericMethodAnalysisContext concrete || !ReferenceEquals(concrete.BaseMethodContext,method)))) return null;
        int? size=null;
        foreach (var variant in closed)
        {
            if (parameter.Index>=variant.TypeGenericParameters.Count || variant.DeclaringType==null) return null;
            var type=variant.TypeGenericParameters[parameter.Index];
            if (!type.IsValueType || type.HasAnyGenericParameters()
                || type is GenericInstanceTypeAnalysisContext {GenericType.FullName:"System.Nullable`1"}) return null;
            var width=TypeSizes.UnboxedSize(type,method.AppContext.Binary.PointerSizeBytes);
            if (width is <=0 or >64 || size!=null && size!=width) return null;
            var target=GenericInstanceFieldLayout.FindInheritedFieldAtOffset(variant.DeclaringType,field.Offset,(int)width);
            if (target==null || !ReferenceEquals(Definition(target),Definition(field.Field))
                || target.FieldType.FullName!=type.FullName) return null;
            size=(int)width;
        }
        return size;
    }

    // Detached shape tests enter here; production must first authenticate the
    // complete original image and concrete native metadata layouts above.
    internal static bool Rewrite(MethodAnalysisContext method,
        Func<GenericParameterTypeAnalysisContext,FieldReference,int?> proveSize)
    {
        var graph=method.ControlFlowGraph!;
        if (!method.IsVoid || method.IsStatic || graph.Instructions.Any(i=>i.OpCode==OpCode.Return && i.Operands.Count!=0)) return false;
        var active=graph.Instructions.Where(i=>i.OpCode is not (OpCode.Nop or OpCode.Jump or OpCode.Return)).ToArray();
        if (active.Length<3 || active[0] is not {OpCode:OpCode.Call,Operands:[Immediate {UnsignedValue:Target},
            LocalVariable pointer,LocalVariable {Type.FullName:"System.Object"} value,RuntimeClassTypeAnalysisContext handle,..]}) return false;
        if (handle.RepresentedType is not GenericParameterTypeAnalysisContext parameter) return false;
        if (pointer.Type!=null || pointer.IsThis || ReferenceEquals(pointer,value)
            || method.ParameterLocals?.Contains(pointer)==true) return false;
        var moves=active.Skip(1).ToArray();
        if (moves.Any(i=>i.OpCode!=OpCode.Move || i.Operands.Count!=2)) return false;
        var fields=moves.Where(i=>i.Operands[0] is FieldReference).ToArray();
        if (fields.Length!=1 || fields[0].Operands[0] is not FieldReference {Parent:null} field
            || !field.Local.IsThis || field.Field.IsStatic || !ReferenceEquals(field.Field.FieldType,parameter)) return false;
        var size=proveSize(parameter,field);
        if (size is not >0 or >64) return false;
        var loads=new Dictionary<LocalVariable,(Instruction Instruction,int Offset,int Width)>();
        var stores=new List<Instruction>();var covered=new HashSet<int>();var beganStores=false;
        foreach (var move in moves)
        {
            if (move.Operands is [LocalVariable temporary,MemoryOperand {Index:null,Scale:0} source]
                && ReferenceEquals(source.Base,pointer))
            {
                if (beganStores || source.Addend<0 || source.Addend>64 || move.NativeReadSize is not (1 or 2 or 4 or 8 or 16)
                    || loads.ContainsKey(temporary)) return false;
                loads[temporary]=(move,(int)source.Addend,move.NativeReadSize);continue;
            }
            if (move.Operands[1] is not LocalVariable chunk || !loads.TryGetValue(chunk,out var loaded)
                || move.NativeWriteSize!=loaded.Width) return false;
            long offset;
            if (ReferenceEquals(move.Operands[0],field)) offset=0;
            else if (move.Operands[0] is MemoryOperand {Index:null,Scale:0} destination
                && ReferenceEquals(destination.Base,field.Local)) offset=destination.Addend-field.Offset;
            else return false;
            if (offset!=loaded.Offset || offset<0 || offset+loaded.Width>size) return false;
            for (var b=(int)offset;b<offset+loaded.Width;b++) if (!covered.Add(b)) return false;
            beganStores=true;stores.Add(move);
        }
        if (covered.Count!=size || stores.Count!=loads.Count || moves.Length!=loads.Count*2) return false;
        // The shape above contains no other pointer/temp consumers, branches,
        // calls or writes. Preserve the checked conversion's original position.
        active[0].OpCode=OpCode.UnboxAny;active[0].SetOperands(pointer,parameter,value);pointer.Type=parameter;
        foreach (var move in moves) {move.OpCode=OpCode.Nop;move.SetOperands();move.NativeReadSize=move.NativeWriteSize=0;}
        fields[0].OpCode=OpCode.Move;fields[0].SetOperands(field,pointer);
        return true;
    }
}
