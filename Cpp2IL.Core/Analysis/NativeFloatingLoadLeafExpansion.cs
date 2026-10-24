using System;
using System.Collections.Concurrent;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Original complete Ghidra1143/1144: scalar LDR S0,[X0,#offset]; RET.
// Preserve the REAL FP return register rather than unknown-call X0 guesses.
// No managed getter/field ownership is inferred by this byte-effect expansion.
public static class NativeFloatingLoadLeafExpansion
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,ConcurrentDictionary<ulong,(int Width,long Offset)>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        var catalog=Catalogs.GetValue(method.AppContext,_=>new());var changed=0;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
        foreach(var block in graph.Blocks)
            for(var index=0;index<block.Instructions.Count;index++)
            {
                var call=block.Instructions[index];
                if(!call.IsCall || call.Operands.Count==0 || call.Operands[0] is not Immediate {Value:>0} address
                    || method.AppContext.MethodsByAddress.ContainsKey(address.UnsignedValue))continue;
                var access=catalog.GetOrAdd(address.UnsignedValue,target=>
                {
                    var binary=method.AppContext.Binary;
                    if(target%4!=0 || !binary.TryMapVirtualAddressToRaw(target,out var raw)
                        || raw<0 || raw>binary.RawLength-8)return default;
                    return Decode(binary.GetRawBinaryContent().Slice((int)raw,8)) ?? default;
                });
                if(Rewrite(block,index,access.Width,access.Offset,ref serial)){index++;changed++;}
            }
        return changed;
    }

    internal static (int Width,long Offset)? Decode(ReadOnlySpan<byte> code)
    {
        if(code.Length<8 || BitConverter.ToUInt32(code[4..8])!=0xd65f03c0)return null;
        var word=BitConverter.ToUInt32(code[..4]);var opcode=word&0xffc003ffu;
        var width=opcode==0xbd400000u?4:opcode==0xfd400000u?8:0;
        return width==0?null:(width,(long)((word>>10)&4095)*width);
    }

    internal static bool Rewrite(Block block,int index,int width,long offset,ref int serial)
    {
        var call=block.Instructions[index];
        if(width is not (4 or 8) || offset<0 || offset%width!=0 || offset/width>4095
            || !NativeStoreLeafExpansion.TryRawReceiver(call,out var receiver))return false;
        var load=new Instruction(serial,OpCode.Move,new Register(null,"V0"),new MemoryOperand(receiver,addend:offset))
            {NativeReadSize=width};
        serial++;block.Instructions.Insert(index,load);
        call.OpCode=OpCode.Nop;call.SetOperands();call.NativeDirectCallTarget=0;
        block.CalculateBlockType();return true;
    }
}
