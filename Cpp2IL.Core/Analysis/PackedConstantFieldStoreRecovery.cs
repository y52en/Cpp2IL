using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// One native constant store can cover several distinct metadata fields. Never
// truncate it to the first field. Unknown/padded/overlapping/reference layouts
// remain unsupported; native compilation still has to reproduce the store.
public static class PackedConstantFieldStoreRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.ControlFlowGraph == null) return 0;
        var serial=method.ControlFlowGraph.Instructions.Select(i=>i.Index).DefaultIfEmpty().Max()+1;
        var count=0;
        foreach(var block in method.ControlFlowGraph.Blocks)
        for(var i=0;i<block.Instructions.Count;i++)
        {
            var instruction=block.Instructions[i];
            if (Split(instruction,method) is not { } pieces) continue;
            instruction.SetOperands(pieces[0].Field,pieces[0].Value);
            instruction.NativeWriteSize=pieces[0].Width;
            for(var j=1;j<pieces.Count;j++)
                block.Instructions.Insert(i+j,new Instruction(serial++,OpCode.Move,pieces[j].Field,pieces[j].Value)
                    {NativeWriteSize=pieces[j].Width});
            i+=pieces.Count-1;count++;
        }
        return count;
    }

    public sealed record Piece(FieldReference Field, Immediate Value, int Width);

    public static IReadOnlyList<Piece>? Split(Instruction instruction,MethodAnalysisContext? nativeMethod=null)
    {
        if(instruction.Operands.FirstOrDefault() is MemoryOperand)
            return SplitClosedValue(instruction,nativeMethod);
        if (instruction is not {OpCode:OpCode.Move,Operands:[FieldReference {Parent:null} first,Immediate value],NativeWriteSize:2 or 4 or 8}
            || first.Local.Type is not {IsValueType:false,GenericParameters.Count:0} owner
            || owner is GenericInstanceTypeAnalysisContext || owner.BaseType?.FullName != "System.Object"
            || !ReferenceEquals(first.Field.DeclaringType,owner) || first.Field.IsStatic
            || first.Offset != first.Field.Offset || first.Offset<16) return null;
        var start=first.Offset;var end=(long)start+instruction.NativeWriteSize;
        var fields=owner.Fields.Where(f=>!f.IsStatic && (f.Attributes&FieldAttributes.Literal)==0).ToArray();
        var covered=new List<(FieldAnalysisContext Field,int Width)>();
        foreach(var field in fields)
        {
            var width=IntegralWidth(field.FieldType);
            if(field.Offset<0)return null;
            if(field.Offset>=end)continue;
            if(width==0)
            {
                // A nonintegral field in/before the store may overlap it.
                return null;
            }
            if((long)field.Offset+width<=start)continue;
            if(field.Offset<start || (long)field.Offset+width>end)return null;
            covered.Add((field,width));
        }
        covered.Sort((a,b)=>a.Field.Offset.CompareTo(b.Field.Offset));
        if(covered.Count<2)return null;
        var cursor=start;var result=new List<Piece>();
        foreach(var (field,width) in covered)
        {
            if(field.Offset!=cursor)return null;
            var bits=(value.UnsignedValue>>((field.Offset-start)*8)) & (ulong.MaxValue>>((8-width)*8));
            var type=field.FieldType.IsEnumType ? field.FieldType.EnumUnderlyingType : field.FieldType;
            if(type == null || type.FullName=="System.Boolean" && bits>1)return null;
            long literal=type.FullName switch
            {
                "System.SByte"=>unchecked((sbyte)bits),
                "System.Int16"=>unchecked((short)bits),
                "System.Int32"=>unchecked((int)bits),
                _=>unchecked((long)bits)
            };
            result.Add(new(new FieldReference(field,first.Local,field.Offset),new Immediate(literal),width));
            cursor+=width;
        }
        return cursor==end ? result : null;
    }

    private static IReadOnlyList<Piece>? SplitClosedValue(Instruction instruction,MethodAnalysisContext? nativeMethod)
    {
        if(instruction is not {OpCode:OpCode.Move,Operands:[MemoryOperand
                {Base:LocalVariable root,Index:null,Scale:0,Addend:>=0} memory,Immediate value],NativeWriteSize:2 or 4 or 8})return null;
        var owner=root.Type is ByRefTypeAnalysisContext byref?byref.ElementType:root.Type;
        if(owner==null || memory.Addend>int.MaxValue-instruction.NativeWriteSize)return null;
        var layout=ClosedGenericValueLayout.Fields(owner,8)
            ??(nativeMethod==null?null:SharedGenericReturnLayout.FieldsFor(nativeMethod,owner));
        if(layout==null)return null;
        var start=memory.Addend;var end=start+instruction.NativeWriteSize;
        var covered=layout.Where(f=>f.Offset<end && f.Offset+f.Size>start).ToArray();
        if(covered.Length<2)return null;
        var cursor=start;var result=new List<Piece>();
        foreach(var storage in covered)
        {
            var field=storage.Field;var width=IntegralWidth(field.FieldType);
            if(width==0 || width!=storage.Size || storage.Offset!=cursor
                || storage.Offset+width>end)return null;
            var bits=(value.UnsignedValue>>checked((int)((storage.Offset-start)*8)))
                &(ulong.MaxValue>>((8-width)*8));
            var type=field.FieldType.IsEnumType?field.FieldType.EnumUnderlyingType:field.FieldType;
            if(type==null || type.FullName=="System.Boolean" && bits>1)return null;
            var literal=type.FullName switch
            {
                "System.SByte"=>unchecked((sbyte)bits),
                "System.Int16"=>unchecked((short)bits),
                "System.Int32"=>unchecked((int)bits),
                _=>unchecked((long)bits)
            };
            result.Add(new(new FieldReference(field,root,checked((int)storage.Offset)),new Immediate(literal),width));
            cursor+=width;
        }
        return cursor==end?result:null;
    }

    private static int IntegralWidth(TypeAnalysisContext? type)
    {
        if(type?.IsEnumType == true)type=type.EnumUnderlyingType;
        return type?.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32"=>4,
            "System.Int64" or "System.UInt64"=>8,
            _=>0
        };
    }
}
