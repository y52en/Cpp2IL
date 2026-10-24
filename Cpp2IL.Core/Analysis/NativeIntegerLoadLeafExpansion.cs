using System;
using System.Collections.Concurrent;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete original Ghidra1553: return *(uint32_t*)X0, LDR W0,[X0];RET.
// Expand machine effects without assigning a managed method/getter identity.
// Same unsigned-immediate LDR grammar as the native instruction lifter; no
// signed/narrow loads, pair loads, volatile/acquire accesses or extra effects.
public static class NativeIntegerLoadLeafExpansion
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
                    || method.AppContext.MethodsByAddress.ContainsKey(address.UnsignedValue)
                    || !HasNullMethodInfo(block,index))continue;
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

    // A native load recipe can also implement a generic Nullable/Enumerator
    // accessor. Its MethodInfo transport is needed by later typed recovery.
    // Do NOT erase that call before metadata propagation. A literal raw X1=0
    // in this same straight-line block is required; missing/merged/aliased
    // metadata or an intervening call/clobber is deliberately left untouched.
    internal static bool HasNullMethodInfo(Block block,int index)
    {
        if(index<0 || index>=block.Instructions.Count || !block.Instructions[index].IsCall)return false;
        for(var n=index-1;n>=0;n--)
        {
            var instruction=block.Instructions[n];
            if(instruction.IsCall || !instruction.IsFallThrough
                || instruction.ImplicitDefinition is Register {Name:"X1"})return false;
            if(instruction.Destination is not Register {Name:"X1"})continue;
            return instruction is {OpCode:OpCode.Move,
                Operands:[Register {Name:"X1",Version:-1},Immediate {Value:0}]};
        }
        return false;
    }

    internal static (int Width,long Offset)? Decode(ReadOnlySpan<byte> code)
    {
        if(code.Length!=8 || BitConverter.ToUInt32(code[4..])!=0xd65f03c0)return null;
        var word=BitConverter.ToUInt32(code[..4]);var opcode=word&0xffc003ffu;
        var width=opcode==0xb9400000u?4:opcode==0xf9400000u?8:0;
        return width==0?null:(width,(long)((word>>10)&4095)*width);
    }

    internal static bool Rewrite(Block block,int index,int width,long offset,ref int serial)
    {
        var call=block.Instructions[index];
        if(width is not (4 or 8) || offset<0 || offset%width!=0 || offset/width>4095
            || !NativeStoreLeafExpansion.TryRawReceiver(call,out var receiver))return false;
        var load=new Instruction(serial,OpCode.Move,new Register(null,"X0"),new MemoryOperand(receiver,addend:offset))
            {NativeReadSize=width};
        serial++;block.Instructions.Insert(index,load);
        // Preserve original instruction identity for incoming branch targets.
        // Raw SSA construction now sees the actual overwritten X0, not a call
        // with sixteen guessed arguments or an invented metadata signature.
        call.OpCode=OpCode.Nop;call.SetOperands();call.NativeDirectCallTarget=0;
        block.CalculateBlockType();return true;
    }
}
