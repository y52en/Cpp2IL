using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A late, independently fingerprinted profile. Never treat arbitrary calls
// behind a metadata-looking bit test as initialization machinery.
public static class LateClassInitRecovery
{
    private const string HelperHash="2A473D0517DE1D832CCC7CED1B25044F3AB2AA106257B4D30BB9486F95AAD174";

    public static bool MatchesBody(ReadOnlySpan<byte> bytes)
    {
        if(bytes.Length!=64)return false;
        using var sha=SHA256.Create();
        return string.Concat(sha.ComputeHash(bytes.ToArray()).Select(b=>b.ToString("X2")))==HelperHash;
    }

    public static int Run(MethodAnalysisContext method)
    {
        var app=method.AppContext;
        if(app.Binary.PointerSizeBytes!=8 || app.UnityVersion.Major!=2018 || app.UnityVersion.Minor!=4)return 0;
        var cfg=method.ControlFlowGraph!;var changes=0;
        var checkedHelpers=new Dictionary<long,bool>();
        bool Known(Instruction call)
        {
            if(call.Operands[0] is not Immediate { Value: >=0 } address)return false;
            if(checkedHelpers.TryGetValue(address.Value,out var known))return known;
            try
            {
                var offset=checked((int)app.Binary.MapVirtualAddressToRaw((ulong)address.Value));
                return checkedHelpers[address.Value]=MatchesBody(app.Binary.GetRawBinaryContent().Slice(offset,64));
            }
            catch(Exception){return checkedHelpers[address.Value]=false;}
        }
        foreach(var guard in cfg.Blocks.ToArray())
            if(TryRecover(cfg,guard,0x126,Known))changes++;
        if(changes!=0){cfg.RemoveUnreachableBlocks();DeadCodeEliminator.Run(cfg);}
        return changes;
    }

    public static bool TryRecover(ISILControlFlowGraph cfg,Block guard,long offset,Func<Instruction,bool> known)
    {
        var defs=cfg.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        if(guard.Successors.Count!=2 || guard.Instructions.LastOrDefault() is not
            {OpCode:OpCode.ConditionalJump,Operands:[Block target,var condition]} || !guard.Successors.Contains(target))return false;
        var invert=false;var seen=new HashSet<LocalVariable>();Instruction? predicate=null;
        condition=Resolve(condition,defs);
        while(condition is LocalVariable local && seen.Add(local) && defs.TryGetValue(local,out predicate))
        {
            if(predicate is {OpCode:OpCode.Not,Operands:[_,LocalVariable operand]}
                && local.Type?.FullName=="System.Boolean" && operand.Type?.FullName=="System.Boolean")
            {invert=!invert;condition=Resolve(operand,defs);continue;}
            break;
        }
        if(predicate is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,
            Operands:[_,LocalVariable bit,Immediate {Value:0}]} || !defs.TryGetValue(bit,out var mask)
            || mask is not {OpCode:OpCode.And,Operands:[_,var flagValue,Immediate {Value:1}]}
            || RuntimeClassFlagSnapshot.Resolve(cfg,guard,mask,flagValue) is not
                MemoryOperand {Index:null,Scale:0,Base:LocalVariable klass} flag
            || flag.Addend!=offset || klass.Type is not RuntimeClassTypeAnalysisContext)return false;
        var initializedOnTarget=(predicate.OpCode==OpCode.CheckNotEqual)!=invert;
        var merge=initializedOnTarget?target:guard.Successors.Single(b=>!ReferenceEquals(b,target));
        var init=guard.Successors.Single(b=>!ReferenceEquals(b,merge));
        var region=new HashSet<Block>();var current=init;var previous=guard;
        while(!ReferenceEquals(current,merge))
        {
            if(current==cfg.EntryBlock || current==cfg.ExitBlock || !region.Add(current) || region.Count>4
                || current.Predecessors.Count!=1 || !ReferenceEquals(current.Predecessors[0],previous)
                || current.Successors.Count!=1)return false;
            previous=current;current=current.Successors[0];
        }
        var regionInstructions=region.SelectMany(b=>b.Instructions).ToHashSet();
        var calls=regionInstructions.Where(i=>i.IsCall).ToArray();
        if(calls.Length!=1 || calls[0].OpCode is not (OpCode.Call or OpCode.CallVoid) || !known(calls[0]))return false;
        var argumentIndex=calls[0].OpCode==OpCode.Call?2:1;
        if(calls[0].Operands.Count<=argumentIndex
            || !ReferenceEquals(Resolve(calls[0].Operands[argumentIndex],defs),Resolve(klass,defs)))return false;
        foreach(var block in region)
        foreach(var instruction in block.Instructions)
        {
            if(ReferenceEquals(instruction,calls[0]) || instruction.OpCode==OpCode.Nop)continue;
            if(instruction.OpCode==OpCode.Jump && ReferenceEquals(instruction,block.Instructions.Last())
                && instruction.Operands is [Block destination] && ReferenceEquals(destination,block.Successors[0]))continue;
            if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable,var source]}
                && source is LocalVariable or Immediate or RuntimeClassTypeAnalysisContext)continue;
            return false;
        }
        var introduced=regionInstructions.Select(i=>i.Destination).OfType<LocalVariable>().ToHashSet();
        if(cfg.Instructions.Where(i=>!regionInstructions.Contains(i)).Any(i=>i.Sources.Any(o=>Contains(o,introduced))))return false;
        cfg.RemoveEdge(guard,init);
        guard.Instructions.Last().OpCode=OpCode.Jump;guard.Instructions.Last().SetOperands(merge);guard.CalculateBlockType();
        cfg.RemoveUnreachableBlocks();return true;
    }

    private static IOperand Resolve(IOperand value,Dictionary<LocalVariable,Instruction> defs)
    {
        var seen=new HashSet<LocalVariable>();
        while(value is LocalVariable local && seen.Add(local) && defs.TryGetValue(local,out var instruction)
            && instruction is {OpCode:OpCode.Move,Operands:[_,var source]})value=source;
        return value;
    }

    private static bool Contains(IOperand operand,HashSet<LocalVariable> locals)=>operand switch
    {
        LocalVariable local=>locals.Contains(local),
        MemoryOperand memory=>(memory.Base!=null && Contains(memory.Base,locals)) || (memory.Index!=null && Contains(memory.Index,locals)),
        FieldReference field=>locals.Contains(field.Local) || (field.Parent!=null && Contains(field.Parent,locals)),
        AddressOf address=>Contains(address.Target,locals),
        ArrayAccess access=>locals.Contains(access.Array) || Contains(access.Index,locals),
        ArrayLength length=>locals.Contains(length.Array),
        _=>false
    };
}
