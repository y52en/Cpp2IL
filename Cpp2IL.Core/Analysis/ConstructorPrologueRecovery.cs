using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Native code can hoist an unobserved local's zero initialization before the
// base constructor. That layout prevents C# initializer recovery. Move ONLY
// proven, non-throwing, unobserved local initializers across a zero-argument
// direct-base call; never move field writes, argument evaluation or callbacks.
public static class ConstructorPrologueRecovery
{
    public static int Run(MethodAnalysisContext method)
        => method.AppContext.UnityVersion.Major == 2018 && method.AppContext.UnityVersion.Minor == 4
           && method.AppContext.Binary.PointerSizeBytes == 8
           && method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet ? Recover(method) : 0;

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.Name!=".ctor" || method.IsStatic || !method.IsVoid
            || method.DeclaringType is not {IsValueType:false} owner || owner.HasAnyGenericParameters()
            || owner.BaseType is not { } parent || parent.HasAnyGenericParameters()
            || method.ControlFlowGraph is not { } cfg || cfg.EntryBlock.Predecessors.Count!=0)return 0;
        var selves=method.ParameterLocals.Where(l=>l.IsThis).ToArray();
        if(selves.Length!=1 || !TrivialConstructorRecovery.SameType(selves[0].Type,owner))return 0;
        var self=selves[0];
        var calls=cfg.Instructions.Where(i=>i.IsCall && i.Operands.Count>1
            && i.Operands[0] is MethodAnalysisContext {Name:".ctor"}
            && i.Operands.Count>(i.OpCode==OpCode.Call?2:1)
            && ReferenceEquals(i.Operands[i.OpCode==OpCode.Call?2:1],self)).ToArray();
        if(calls.Length!=1 || calls[0] is not {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
            Operands:[MethodAnalysisContext target,LocalVariable receiver]}
            || !ReferenceEquals(receiver,self) || target.IsStatic || target.IsVirtual || !target.IsVoid
            || target.Parameters.Count!=0 || !TrivialConstructorRecovery.SameType(target.DeclaringType,parent))return 0;
        var call=calls[0];var blocks=cfg.Blocks.Where(b=>b.Instructions.Contains(call)).ToArray();
        if(blocks.Length!=1)return 0;
        var block=blocks[0];
        if(block.Successors.Count!=1)return 0; // no exceptional/bypass successor can observe the old local
        var path=cfg.EntryBlock;var visited=new HashSet<Block>();
        while(!ReferenceEquals(path,block))
        {
            if(!visited.Add(path) || path.Instructions.Any(i=>i.OpCode is not (OpCode.Nop or OpCode.Jump))
                || path.Successors.Count!=1 || path.Successors[0].Predecessors.Count!=1)return 0;
            path=path.Successors[0];
        }
        var prefix=block.Instructions.Take(block.Instructions.IndexOf(call)).Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(prefix.Length>128)return 0;
        var moves=new List<Instruction>();
        foreach(var instruction in prefix)
        {
            if(instruction is {OpCode:OpCode.Move,Operands:[FieldReference {Parent:null} field,var constant]}
                && ReferenceEquals(field.Local,self) && ReferenceEquals(field.Field.DeclaringType,owner)
                && constant is Immediate or FloatLiteral or DoubleLiteral or DefaultStructValue)continue;
            if(instruction is not {OpCode:OpCode.Move,Operands:[LocalVariable local,var value]}
                || method.ParameterLocals.Contains(local) || local.IsThis || !Pure(instruction,local,value,method)
                || cfg.Instructions.Count(i=>ReferenceEquals(i.Destination,local))!=1
                || prefix.Where(i=>!ReferenceEquals(i,instruction)).SelectMany(i=>i.Operands)
                    .Any(o=>References(o,local)))return 0;
            moves.Add(instruction);
        }
        if(moves.Count==0)return 0;
        foreach(var move in moves)block.Instructions.Remove(move);
        block.Instructions.InsertRange(block.Instructions.IndexOf(call)+1,moves);
        block.CalculateBlockType();
        return moves.Count;
    }

    private static bool Pure(Instruction instruction,LocalVariable local,IOperand value,MethodAnalysisContext method)
    {
        if(instruction.ImplicitDefinition!=null || local.Type is null
            || local.Type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext)return false;
        if(value is DefaultStructValue zero && zero.Type.IsValueType && !zero.Type.HasAnyGenericParameters()
            && TrivialConstructorRecovery.SameType(local.Type,zero.Type))
        {
            var size=TypeSizes.UnboxedSize(zero.Type,method.AppContext.Binary.PointerSizeBytes);
            return size>0 && (instruction.NativeWriteSize==size || instruction.NativeZeroSize>=size);
        }
        return value switch
        {
            Immediate n => TypeSizes.IsScalarValueType(local.Type) || !local.Type.IsValueType && n.Value==0,
            FloatLiteral => local.Type.FullName=="System.Single",
            DoubleLiteral => local.Type.FullName=="System.Double",
            _ => false
        };
    }

    private static bool References(IOperand operand,LocalVariable local)=>operand switch
    {
        LocalVariable l=>ReferenceEquals(l,local),
        AddressOf a=>References(a.Target,local),
        MemoryOperand m=>m.Base!=null && References(m.Base,local) || m.Index!=null && References(m.Index,local),
        FieldReference f=>ReferenceEquals(f.Local,local) || f.Parent!=null && References(f.Parent,local),
        ArrayAccess a=>ReferenceEquals(a.Array,local) || References(a.Index,local),
        ArrayLength a=>ReferenceEquals(a.Array,local),
        _=>false
    };
}
