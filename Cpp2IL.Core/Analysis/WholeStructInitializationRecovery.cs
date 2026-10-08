using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

public static class WholeStructInitializationRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is not NewArmV8InstructionSet) return false;
        var graph=method.ControlFlowGraph!;
        var targets=new List<(Register Storage,TypeAnalysisContext Type,Block Block,Instruction Call)>();
        foreach(var block in graph.Blocks)
        foreach(var call in block.Instructions)
        {
            if(!call.IsCall || call.Operands[0] is not Immediate address
                || !method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue,out var callees)
                || callees.Count!=1 || callees[0] is not {IsStatic:false,DeclaringType.IsValueType:true} callee) continue;
            var first=call.OpCode==OpCode.CallVoid?1:2;
            if(call.Operands.Count<=first) continue;
            var storage=call.Operands[first] switch
            {
                AddressOf {Target:Register direct}=>direct,
                Register pointer=>HiddenStructReturnRecovery.ResolveStackAddress(block,block.Instructions.IndexOf(call),pointer),
                _=>(Register?)null
            };
            if(storage is { } slot && Offset(slot,out _)) targets.Add((slot,callee.DeclaringType,block,call));
        }
        DominatorInfo? dominance=null;
        var changed=false;
        foreach(var group in targets.GroupBy(t=>t.Storage.Name))
        {
            var types=group.Select(t=>t.Type).Distinct().ToArray();
            if(types.Length!=1) continue; // reused storage with ambiguous type
            var target=group.First();
            var size=TypeSizes.UnboxedSize(target.Type,method.AppContext.Binary.PointerSizeBytes);
            if(size<=0 || size>int.MaxValue) continue;
            foreach(var block in graph.Blocks)
            for(var start=0;start<block.Instructions.Count;start++)
            {
                if(block.Instructions[start].NativeWriteSize==0) continue;
                if(!group.Any(t=>block==t.Block
                    ? start<block.Instructions.IndexOf(t.Call)
                    : (dominance??=new DominatorInfo(graph)).Dominates(block,t.Block))) continue;
                changed |= RecoverGroup(block,start,target.Storage,target.Type,(int)size);
            }
        }
        return changed;
    }

    public static bool RecoverGroup(Block block,int start,Register storage,TypeAnalysisContext type,int size)
    {
        if(!type.IsValueType || size<=0 || !Offset(storage,out var basis)) return false;
        var bytes=new HashSet<long>();var stores=new List<Instruction>();
        for(var i=start;i<block.Instructions.Count;i++)
        {
            var instruction=block.Instructions[i];
            if(instruction.OpCode==OpCode.Nop) continue;
            if(instruction is not {OpCode:OpCode.Move,Operands:[Register slot,Immediate {Value:0}]}
                || instruction.NativeWriteSize is not (1 or 2 or 4 or 8 or 16)
                || !Offset(slot,out var offset)) return false;
            var delta=(long)offset-basis;
            if(delta<0 || delta+instruction.NativeWriteSize>size) return false;
            for(var b=0;b<instruction.NativeWriteSize;b++)
                if(!bytes.Add(delta+b)) return false; // overlap is not proof of more bytes
            stores.Add(instruction);
            if(bytes.Count!=size) continue;
            stores[0].SetOperands(storage,new DefaultStructValue(type));
            stores[0].NativeWriteSize=0;
            foreach(var other in stores.Skip(1)){other.OpCode=OpCode.Nop;other.SetOperands();other.NativeWriteSize=0;}
            return true;
        }
        return false;
    }

    private static bool Offset(Register register,out int offset)
    {
        offset=0;var name=register.Name;
        if(!name.StartsWith("stack_",System.StringComparison.Ordinal)) return false;
        var text=name.Substring(6);var negative=text.StartsWith("-",System.StringComparison.Ordinal);
        if(negative) text=text.Substring(1);
        if(!int.TryParse(text,NumberStyles.AllowHexSpecifier,CultureInfo.InvariantCulture,out var value)||value<0) return false;
        offset=negative?-value:value;return true;
    }
}
