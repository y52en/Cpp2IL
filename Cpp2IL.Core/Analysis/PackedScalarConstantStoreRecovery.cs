using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Native integer bits can represent a packed enum/integer/float FIELD STORE,
// not arithmetic. Use complete unique metadata lanes, never guessed offsets.
// Native access width/atomicity is not established until the rebuilt code and
// every global gate pass. No references, padding, partial fields or NaN payloads.
public static class PackedScalarConstantStoreRecovery
{
    public static int Run(MethodAnalysisContext method)
        =>CheckedUnboxRecovery.Supports(method.AppContext)?Recover(method):0;

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;var count=0;
        foreach(var block in graph.Blocks)
        for(var n=0;n<block.Instructions.Count;n++)
        {
            var store=block.Instructions[n];
            if(store is not {OpCode:OpCode.Move,NativeReadSize:0,NativeWriteSize:2 or 4 or 8,
                    Operands:[var destination,Immediate value]}
                ||PackedPrimitiveFieldCopyRecovery.Address(destination) is not {} address)continue;
            var options=new[]{1,2,4,8}.Select(w=>(Width:w,Fields:PackedPrimitiveFieldCopyRecovery.Fields(method,address,store.NativeWriteSize,w)))
                .Where(p=>p.Fields is {Length:>1}).ToArray();
            if(options.Length!=1)continue;
            var width=options[0].Width;var fields=options[0].Fields!;
            var literals=new List<IOperand>();
            for(var lane=0;lane<fields.Length;lane++)
            {
                var bits=(value.UnsignedValue>>(lane*width*8))&(ulong.MaxValue>>((8-width)*8));
                var type=fields[lane].Field.FieldType;
                if(type.IsEnumType)type=type.EnumUnderlyingType!;
                IOperand? literal=type?.FullName switch {
                    "System.Boolean" when bits<=1=>new Immediate((long)bits),
                    "System.Byte" or "System.Char" or "System.UInt16" or "System.UInt32"=>new Immediate((long)bits),
                    "System.SByte"=>new Immediate(unchecked((sbyte)bits)),
                    "System.Int16"=>new Immediate(unchecked((short)bits)),
                    "System.Int32"=>new Immediate(unchecked((int)bits)),
                    "System.Int64" or "System.UInt64"=>new Immediate(unchecked((long)bits)),
                    "System.Single" when float.IsFinite(BitConverter.Int32BitsToSingle(unchecked((int)bits)))
                        =>new FloatLiteral(BitConverter.Int32BitsToSingle(unchecked((int)bits))),
                    _=>null
                };
                if(literal==null)break;
                literals.Add(literal);
            }
            if(literals.Count!=fields.Length)continue; // ALL byte/type/value checks before mutation.
            store.SetOperands(fields[0],literals[0]);store.NativeWriteSize=width;store.NativeFloatingPointSize=0;
            for(var lane=1;lane<fields.Length;lane++)
                block.Instructions.Insert(n+lane,new Instruction(serial++,OpCode.Move,fields[lane],literals[lane]){NativeWriteSize=width});
            n+=fields.Length-1;block.CalculateBlockType();count++;
        }
        return count;
    }
}
