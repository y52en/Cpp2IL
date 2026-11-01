using System;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A primitive's private m_value is its entire unboxed storage, not a source-
// accessible member. Keep the managed pointer and emit ldobj/stobj instead.
public static class PrimitiveByRefStorageRecovery
{
    public static int Run(MethodAnalysisContext method)
        =>method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            && method.AppContext.Binary.PointerSizeBytes==8?Recover(method):0;

    private static int Width(TypeAnalysisContext owner,SystemTypesContext types)
    {
        var (canonical,width)=owner.FullName switch {
            "System.Boolean"=>(types.SystemBooleanType,1),"System.Byte"=>(types.SystemByteType,1),
            "System.SByte"=>(types.SystemSByteType,1),"System.Char"=>(types.SystemCharType,2),
            "System.Int16"=>(types.SystemInt16Type,2),"System.UInt16"=>(types.SystemUInt16Type,2),
            "System.Int32"=>(types.SystemInt32Type,4),"System.UInt32"=>(types.SystemUInt32Type,4),
            "System.Int64"=>(types.SystemInt64Type,8),"System.UInt64"=>(types.SystemUInt64Type,8),
            "System.Single"=>(types.SystemSingleType,4),"System.Double"=>(types.SystemDoubleType,8),
            _=>((TypeAnalysisContext?)null,0)};
        return ReferenceEquals(owner,canonical)?width:0;
    }

    private static bool Storage(FieldReference field,int nativeWidth,MethodAnalysisContext method)
    {
        if(field.Parent!=null || field.Offset!=0 || field.Field.IsStatic || field.Field.Offset!=0
            || field.Field.Name!="m_value" || field.Field.BackingData==null
            || field.Local.Type is not ByRefTypeAnalysisContext {ElementType:{} referent}
            || !ReferenceEquals(referent,field.Field.DeclaringType)
            || !ReferenceEquals(referent,field.Field.FieldType))return false;
        var width=Width(referent,method.AppContext.SystemTypes);
        return width>0 && nativeWidth==width && TypeSizes.UnboxedSize(referent,method.AppContext.Binary.PointerSizeBytes)==width
            && referent.Fields.Where(f=>!f.IsStatic).ToArray() is [var only] && ReferenceEquals(only,field.Field);
    }

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} cfg)return 0;
        var count=0;
        foreach(var instruction in cfg.Instructions)
        {
            if(instruction is not {OpCode:OpCode.Move,Operands:[var destination,var source]})continue;
            if(destination is FieldReference target && Storage(target,instruction.NativeWriteSize,method))
            {instruction.SetOperand(0,new MemoryOperand(target.Local));count++;}
            if(source is FieldReference value && Storage(value,instruction.NativeReadSize,method))
            {instruction.SetOperand(1,new MemoryOperand(value.Local));count++;}
        }
        return count;
    }
}
