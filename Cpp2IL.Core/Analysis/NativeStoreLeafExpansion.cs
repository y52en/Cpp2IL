using System;
using System.Collections.Concurrent;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete original native leaf effects, NOT guessed constructor identities.
// Ghidra primary1093/1100/1175/1201: exact scalar/zero store leaves.
// Expansion precedes stack analysis so each real write reaches its own slot.
public static class NativeStoreLeafExpansion
{
    private static readonly byte[] Pair=Convert.FromHexString("0004002dc0035fd6");
    private static readonly byte[] Triple=Convert.FromHexString("0004002d020800bdc0035fd6");
    private static readonly byte[] Quad=Convert.FromHexString("0004002d020c012dc0035fd6");
    private static readonly byte[] PairZero=Convert.FromHexString("0004002d1f0800b9c0035fd6");
    internal readonly record struct StoreRecipe(int FloatingLanes,int ZeroLanes=0)
    {
        public int Count=>FloatingLanes+ZeroLanes;
    }
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,ConcurrentDictionary<ulong,StoreRecipe>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph || !CheckedUnboxRecovery.Supports(method.AppContext))return 0;
        // Reuse ONLY the independently hash-verified original ARM64 image
        // profile above; this pass does not use or infer unbox semantics.
        var catalog=Catalogs.GetValue(method.AppContext,_=>new());var changed=0;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
        foreach(var block in graph.Blocks)
            for(var index=0;index<block.Instructions.Count;index++)
            {
                var call=block.Instructions[index];
                if(!call.IsCall || call.Operands.Count==0 || call.Operands[0] is not Immediate {Value:>0} address
                    || method.AppContext.MethodsByAddress.ContainsKey(address.UnsignedValue))continue;
                var recipe=catalog.GetOrAdd(address.UnsignedValue,target=>
                {
                    var binary=method.AppContext.Binary;
                    if(target%4!=0 || !binary.TryMapVirtualAddressToRaw(target,out var raw)
                        || raw<0 || raw>binary.RawLength-Pair.Length)return default;
                    var content=binary.GetRawBinaryContent();
                    return MatchRecipe(content.Slice((int)raw,(int)Math.Min(Quad.Length,binary.RawLength-raw)));
                });
                if(Rewrite(block,index,recipe,ref serial)) {index+=recipe.Count;changed++;}
            }
        return changed;
    }

    internal static int LaneCount(ReadOnlySpan<byte> code)
        =>MatchRecipe(code).Count;

    internal static StoreRecipe MatchRecipe(ReadOnlySpan<byte> code)
        => code.Length>=Quad.Length && code[..Quad.Length].SequenceEqual(Quad)?new(4):
           code.Length>=Triple.Length && code[..Triple.Length].SequenceEqual(Triple)?new(3):
           code.Length>=PairZero.Length && code[..PairZero.Length].SequenceEqual(PairZero)?new(2,1):
           code.Length>=Pair.Length && code[..Pair.Length].SequenceEqual(Pair)?new(2):default;

    internal static bool Rewrite(Block block,int index,int lanes,ref int serial)
        =>Rewrite(block,index,new StoreRecipe(lanes),ref serial);

    internal static bool Rewrite(Block block,int index,StoreRecipe recipe,ref int serial)
    {
        var call=block.Instructions[index];
        if(!(recipe.ZeroLanes==0 && recipe.FloatingLanes is 2 or 3 or 4
                || recipe is {FloatingLanes:2,ZeroLanes:1}) || !TryRawReceiver(call,out var receiver))return false;
        var first=call.OpCode==OpCode.Call?2:1;
        var start=serial;
        var stores=Enumerable.Range(0,recipe.Count).Select(n=>new Instruction(start+n,OpCode.Move,
            new MemoryOperand(receiver,addend:n*4),n<recipe.FloatingLanes?call.Operands[first+8+n]:new Immediate(0))
            {NativeWriteSize=4}).ToArray();
        // Keep the original instruction identity for any branch target. X0
        // is unchanged by these complete leaves; do not synthesize a return.
        serial+=recipe.Count;block.Instructions.InsertRange(index,stores);
        call.OpCode=OpCode.Nop;call.SetOperands();call.NativeDirectCallTarget=0;
        block.CalculateBlockType();return true;
    }

    internal static bool TryRawReceiver(Instruction call,out Register receiver)
    {
        receiver=default;
        if(!call.IsCall || call.Operands.Count==0 || call.NativeVirtualDispatch || call.ImplicitDefinition!=null
            || call.Operands[0] is not Immediate {Value:>0})return false;
        if(call.NativeDirectCallTarget!=0 && call.NativeDirectCallTarget!=((Immediate)call.Operands[0]).UnsignedValue)return false;
        var first=call.OpCode==OpCode.Call?2:1;
        if(call.Operands.Count!=first+16)return false;
        for(var n=0;n<16;n++)
            if(call.Operands[first+n] is not Register {Version:-1} register
                || register.Name!=(n<8?"X"+n:"V"+(n-8)))return false;
        receiver=(Register)call.Operands[first];
        if(call.OpCode==OpCode.Call && (call.Operands[1] is not Register destination || !destination.Equals(receiver)))return false;
        return true;
    }
}
