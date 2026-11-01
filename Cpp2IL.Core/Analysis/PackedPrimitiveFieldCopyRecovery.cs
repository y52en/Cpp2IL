using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A packed register used ONLY as copied storage is not a double/object value.
// Reconstruct exact metadata scalar lanes at the original read/store positions.
// Keep all loads before their original stores (including overlapping objects).
// Final native validation must still prove the packed access/atomicity matches.
public static class PackedPrimitiveFieldCopyRecovery
{
    public static int Run(MethodAnalysisContext method)
        =>CheckedUnboxRecovery.Supports(method.AppContext)?Recover(method):0;

    private static bool References(IOperand? operand,LocalVariable local,HashSet<FieldReference>? seen=null)
    {
        if(ReferenceEquals(operand,local))return true;
        return operand switch
        {
            MemoryOperand m=>References(m.Base,local)||References(m.Index,local),
            FieldReference f=>ReferenceEquals(f.Local,local)||(seen??=new()).Add(f)&&References(f.Parent,local,seen),
            AddressOf a=>References(a.Target,local),
            ArrayAccess a=>ReferenceEquals(a.Array,local)||References(a.Index,local),
            ArrayLength a=>ReferenceEquals(a.Array,local),_=>false
        };
    }

    internal static MemoryOperand? Address(IOperand operand)
    {
        if(operand is MemoryOperand memory)return memory;
        if(operand is not FieldReference field)return null;
        var seen=new HashSet<FieldReference>();long offset=0;var root=field.Local;
        for(var current=field;current!=null;current=current.Parent)
        {
            if(!seen.Add(current)||seen.Count>8||!ReferenceEquals(current.Local,root)
                ||current.Offset<0||offset>long.MaxValue-current.Offset
                ||current.Parent!=null&&!current.Parent.Field.FieldType.IsValueType)return null;
            offset+=current.Offset;
        }
        return new MemoryOperand(root,addend:offset);
    }

    private static bool Scalar(TypeAnalysisContext type,int width)
    {
        if(type.IsEnumType)return type.EnumUnderlyingType is {} underlying&&Scalar(underlying,width);
        return width switch
        {
            1=>type.FullName is "System.Boolean" or "System.Byte" or "System.SByte",
            2=>type.FullName is "System.Char" or "System.Int16" or "System.UInt16",
            4=>type.FullName is "System.Single" or "System.Int32" or "System.UInt32",
            8=>type.FullName is "System.Double" or "System.Int64" or "System.UInt64",_=>false
        };
    }

    internal static FieldReference[]? Fields(MethodAnalysisContext method,MemoryOperand memory,int width,int laneWidth)
    {
        if(memory is not {Base:LocalVariable {Type:{} type} root,Index:null,Scale:0}
            ||type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            ||memory.Addend<0||memory.Addend>long.MaxValue-width||width%laneWidth!=0)return null;
        var fields=new List<FieldReference>();
        for(var offset=0;offset<width;offset+=laneWidth)
        {
            var field=NestedFieldAccess.Find(type,root,memory.Addend+offset,laneWidth,method);
            if(field==null||!Scalar(field.Field.FieldType,laneWidth)
                ||TypeSizes.UnboxedSize(field.Field.FieldType,8)!=laneWidth)return null;
            fields.Add(field);
        }
        return fields.ToArray();
    }

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var original=graph.Instructions.ToArray();var dominance=new DominatorInfo(graph);
        var blocks=graph.Blocks.SelectMany(b=>b.Instructions.Select(i=>(i,b))).ToDictionary(p=>p.i,p=>p.b);
        var serial=original.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;var count=0;
        foreach(var load in original)
        {
            if(load is not {OpCode:OpCode.Move,NativeReadSize:4 or 8 or 16,NativeWriteSize:0,
                    Operands:[LocalVariable chunk,var sourceOperand]}
                ||Address(sourceOperand) is not {} source||References(sourceOperand,chunk))continue;
            // Most native pointer loads cannot be scalar-copy lanes; reject
            // those before the more expensive whole-graph def/use checks.
            var options=new[]{1,2,4,8}.Select(w=>(Width:w,Fields:Fields(method,source,load.NativeReadSize,w)))
                .Where(p=>p.Fields is {Length:>1}).ToArray();
            if(options.Length!=1||chunk.IsThis||chunk.IsMethodInfo||method.ParameterLocals.Contains(chunk)
                ||graph.Instructions.Count(i=>ReferenceEquals(i.Destination,chunk))!=1)continue;
            var uses=graph.Instructions.Where(i=>!ReferenceEquals(i,load)&&i.Operands.Any(o=>References(o,chunk))).ToArray();
            if(uses.Length==0||uses.Any(i=>i is not {OpCode:OpCode.Move,NativeReadSize:0,
                    Operands:[var destination,LocalVariable stored]}||!ReferenceEquals(stored,chunk)
                ||i.NativeWriteSize!=load.NativeReadSize||Address(destination)==null||References(destination,chunk)))continue;
            var origin=blocks[load];
            if(uses.Any(i=>!dominance.Dominates(origin,blocks[i])||ReferenceEquals(origin,blocks[i])
                &&origin.Instructions.IndexOf(i)<=origin.Instructions.IndexOf(load)))continue;
            var laneWidth=options[0].Width;var sourceFields=options[0].Fields!;
            var targets=uses.Select(i=>Fields(method,Address(i.Operands[0])!.Value,load.NativeReadSize,laneWidth)).ToArray();
            if(targets.Any(d=>d==null||d.Length!=sourceFields.Length||d.Where((f,n)=>
                !TrivialConstructorRecovery.SameType(f.Field.FieldType,sourceFields[n].Field.FieldType)).Any()))continue;
            // No mutation until EVERY consumer and byte/metadata lane passed.
            var values=sourceFields.Select(f=>new LocalVariable("packed_lane_"+serial++,
                new Register(null,"PACKED_LANE_"+serial),f.Field.FieldType)).ToArray();
            var reads=values.Select((v,n)=>new Instruction(serial++,OpCode.Move,v,sourceFields[n]){NativeReadSize=laneWidth}).ToArray();
            method.Locals.AddRange(values);origin.Instructions.InsertRange(origin.Instructions.IndexOf(load),reads);
            for(var consumer=0;consumer<uses.Length;consumer++)
            {
                var store=uses[consumer];var block=blocks[store];
                var writes=values.Select((v,n)=>new Instruction(serial++,OpCode.Move,targets[consumer]![n],v){NativeWriteSize=laneWidth}).ToArray();
                block.Instructions.InsertRange(block.Instructions.IndexOf(store),writes);
                Clear(store);block.CalculateBlockType();
            }
            Clear(load);origin.CalculateBlockType();count++;
        }
        return count;
    }

    private static void Clear(Instruction instruction)
    {
        instruction.OpCode=OpCode.Nop;instruction.SetOperands();
        instruction.NativeReadSize=instruction.NativeWriteSize=instruction.NativeFloatingPointSize=0;
    }
}
