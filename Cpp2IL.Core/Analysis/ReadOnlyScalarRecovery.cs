using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

public static class ReadOnlyScalarRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary is not ElfFile binary) return 0;
        var changed = 0;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [var target, MemoryOperand memory] }
                || !memory.IsConstant || memory.Addend <= 0) continue;
            if(target is FieldReference && instruction.NativeWriteSize>0
                && instruction.NativeWriteSize!=instruction.NativeReadSize) continue;
            var type = target switch { LocalVariable local => local.Type,
                FieldReference field => field.Field.FieldType, _ => null };
            if (type?.IsEnumType == true) type = type.EnumUnderlyingType;
            if (type == null || !Supports(type.FullName,instruction.NativeReadSize)
                || !binary.TryReadReadOnlyScalar((ulong)memory.Addend,instruction.NativeReadSize,out var bits)) continue;
            if (Decode(type.FullName,instruction.NativeReadSize,bits) is not { } literal) continue;
            instruction.SetOperand(1,literal); changed++;
        }
        var serial=method.ControlFlowGraph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
        foreach(var block in method.ControlFlowGraph.Blocks)
        for(var at=0;at<block.Instructions.Count;at++)
        {
            var instruction=block.Instructions[at];
            var stores=ProjectWideStore(instruction,binary.TryReadReadOnlyScalar)
                ?? ProjectWideSnapshot(method.ControlFlowGraph,block,instruction,binary.TryReadReadOnlyScalar);
            if(stores==null)continue;
            instruction.SetOperands(stores[0].Field,stores[0].Value);
            instruction.NativeReadSize=0;instruction.NativeWriteSize=stores[0].Width;
            for(var n=1;n<stores.Count;n++)
                block.Instructions.Insert(at+n,new Instruction(serial++,OpCode.Move,stores[n].Field,stores[n].Value)
                    {NativeWriteSize=stores[n].Width});
            at+=stores.Count-1;changed++;
        }
        return changed;
    }

    public delegate bool ScalarReader(ulong address,int width,out ulong bits);
    public sealed record ScalarStore(FieldReference Field,IOperand Value,int Width);

    public static List<ScalarStore>? ProjectWideSnapshot(ISILControlFlowGraph cfg,Block block,Instruction instruction,ScalarReader read)
    {
        if(instruction is not {OpCode:OpCode.Move,Operands:[FieldReference target,LocalVariable source],NativeWriteSize:8 or 16})return null;
        var definitions=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,source)).ToArray();
        if(definitions.Length!=1 || definitions[0] is not {OpCode:OpCode.Move,Operands:[_,MemoryOperand memory]} load
            || load.NativeReadSize!=instruction.NativeWriteSize || !memory.IsConstant
            || !block.Instructions.Contains(load))return null;
        var start=block.Instructions.IndexOf(load);var end=block.Instructions.IndexOf(instruction);
        if(start<0 || end<=start || block.Instructions.Skip(start+1).Take(end-start-1).Any(i=>i.IsCall)
            || cfg.Instructions.Any(i=>i.Operands.Any(o=>o is AddressOf {Target:LocalVariable addressed}
                && ReferenceEquals(addressed,source))))return null;
        // Recognition only. The original vector load remains if other real
        // consumers need it; ordinary DCE can drop it only after the final use.
        var projected=new Instruction(instruction.Index,OpCode.Move,target,memory)
            {NativeReadSize=load.NativeReadSize,NativeWriteSize=instruction.NativeWriteSize};
        return ProjectWideStore(projected,read);
    }

    // SIMD/paired literal stores may initialize multiple metadata fields. Never
    // reinterpret the entire store as only the first field, or infer padding.
    public static List<ScalarStore>? ProjectWideStore(Instruction instruction,ScalarReader read)
    {
        if(instruction is not {OpCode:OpCode.Move,Operands:[FieldReference target,MemoryOperand memory]}
            || instruction.NativeWriteSize is not (8 or 16) || instruction.NativeReadSize!=instruction.NativeWriteSize
            || target.Parent!=null || target.Field.IsStatic || !memory.IsConstant || memory.Addend<=0
            || target.Offset!=target.Field.Offset || target.Offset<0
            || target.Offset>int.MaxValue-instruction.NativeWriteSize
            || !TrivialConstructorRecovery.SameType(target.Local.Type,target.Field.DeclaringType)) return null;
        var end=target.Offset+instruction.NativeWriteSize;
        var fields=target.Field.DeclaringType.Fields.Where(f=>!f.IsStatic && f.Offset>=target.Offset && f.Offset<end)
            .OrderBy(f=>f.Offset).ToArray();
        if(fields.Length<2 || !ReferenceEquals(fields[0],target.Field)) return null;
        var stores=new List<ScalarStore>();var offset=target.Offset;
        foreach(var field in fields)
        {
            var type=field.FieldType.IsEnumType?field.FieldType.EnumUnderlyingType:field.FieldType;
            var width=type==null?0:Supports(type.FullName,4)?4:Supports(type.FullName,8)?8:0;
            if(width==0 || field.Offset!=offset || width>end-offset
                || !read((ulong)memory.Addend+(ulong)(offset-target.Offset),width,out var bits)
                || Decode(type!.FullName,width,bits) is not { } value) return null;
            stores.Add(new(new FieldReference(field,target.Local,offset),value,width));offset+=width;
        }
        return offset==end?stores:null;
    }

    public static bool Supports(string type,int width) => (type,width) is
        ("System.Int32" or "System.UInt32" or "System.Single",4)
        or ("System.Int64" or "System.UInt64" or "System.Double",8);

    public static IOperand? Decode(string type,int width,ulong bits)
    {
        if (!Supports(type,width)) return null;
        return type switch {
            "System.Single" => new FloatLiteral(BitConverter.ToSingle(BitConverter.GetBytes((uint)bits),0)),
            "System.Double" => new DoubleLiteral(BitConverter.ToDouble(BitConverter.GetBytes(bits),0)),
            "System.Int32" => new Immediate(unchecked((int)bits)),
            "System.UInt32" => new Immediate((long)(uint)bits),
            _ => new Immediate(unchecked((long)bits)) };
    }
}
