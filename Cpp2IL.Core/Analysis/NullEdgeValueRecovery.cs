using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// After SSA destruction a null reference can feed an integral result phi.
// The synthetic copy executes before its null branch, but its value is live
// only on the null edge: EVERY other path kills it before a read/escape.
// Replace that copy's source by zero; never cast an arbitrary reference to int.
public static class NullEdgeValueRecovery
{
    static bool Integral(TypeAnalysisContext? type)=>(type?.IsEnumType==true?type.EnumUnderlyingType:type)?.FullName is
        "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char" or "System.Int16" or "System.UInt16"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64";

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph)return 0;
        var defs=graph.Instructions.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var changed=0;
        foreach(var guard in graph.Blocks)
        {
            if(guard.Successors.Count!=2||guard.Successors.Distinct().Count()!=2
                ||guard.Instructions.LastOrDefault() is not {OpCode:OpCode.ConditionalJump,Operands:[Block target,LocalVariable condition]}
                ||!guard.Successors.Contains(target))continue;
            var inverted=false;var seen=new HashSet<LocalVariable>();var flag=condition;Instruction? predicate=null;
            while(seen.Count<8&&seen.Add(flag)&&flag.Type?.FullName=="System.Boolean"&&defs.TryGetValue(flag,out var definition)
                &&guard.Instructions.Contains(definition))
            {
                if(definition is {OpCode:OpCode.Not,Operands:[_,LocalVariable previous]})
                {inverted=!inverted;flag=previous;continue;}
                predicate=definition;break;
            }
            if(predicate is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,Operands:[_,var a,var b]})continue;
            if(predicate.NativeComparisonSize!=method.AppContext.Binary.PointerSizeBytes||predicate.NativeIntegerSourceView)continue;
            var source=a is Immediate {Value:0}?b as LocalVariable:b is Immediate {Value:0}?a as LocalVariable:null;
            if(source?.Type is not {IsValueType:false}||source.Type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                ||source.Type.Type is not (LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_CLASS
                    or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_STRING
                    or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_ARRAY
                    or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST)
                ||!InlineClassTestRecovery.StableSource(method,source,guard)
                ||graph.Instructions.Any(i=>i.Operands.Any(o=>AddressEscapes(o,source))))continue;
            if(defs.TryGetValue(source,out var sourceWrite)&&!ForwardNullCheckRecovery.DefinitionDominates(graph,sourceWrite,predicate))continue;
            var nullBranch=(predicate.OpCode==OpCode.CheckEqual)!=inverted;
            var nonnull=nullBranch?guard.Successors.Single(b=>!ReferenceEquals(b,target)):target;
            for(var n=0;n<guard.Instructions.Count-1;n++)
            {
                var copy=guard.Instructions[n];
                if(copy is not {Index:-1,OpCode:OpCode.Move,ImplicitDefinition:null,NativeReadSize:0,NativeWriteSize:0,
                    NativeRegisterCopySize:0,NativeIntegerSourceView:false,Operands:[LocalVariable output,LocalVariable input]}
                    ||!ReferenceEquals(input,source)||!Integral(output.Type)||ReferenceEquals(output,source)
                    ||copy.NativeArithmeticSize!=0||copy.NativeFloatingPointSize!=0
                    ||graph.Instructions.Any(i=>i.Operands.Any(o=>AddressEscapes(o,output))))continue;
                if(sourceWrite!=null&&!ForwardNullCheckRecovery.DefinitionDominates(graph,sourceWrite,copy))continue;
                var tail=guard.Instructions.Skip(n+1).ToArray();
                if(tail.Any(i=>Reads(i,output)||ReferenceEquals(i.Destination,output)))continue;
                if(!DeadUntilKilled(nonnull,output,new HashSet<Block>(),new Dictionary<Block,bool>()))continue;
                copy.SetOperand(1,new Immediate(0));changed++;
            }
        }
        return changed;
    }
    static bool DeadUntilKilled(Block block,LocalVariable local,HashSet<Block> visiting,Dictionary<Block,bool> memo)
    {
        if(memo.TryGetValue(block,out var result))return result;
        if(!visiting.Add(block))return false;
        foreach(var instruction in block.Instructions)
        {
            if(instruction.OpCode is OpCode.Phi or OpCode.IndirectCall or OpCode.IndirectJump
                ||instruction.IsCall&&instruction.Operands[0]is not MethodAnalysisContext
                ||Reads(instruction,local))return false;
            if(ReferenceEquals(instruction.Destination,local))
            {visiting.Remove(block);memo[block]=true;return true;}
        }
        result=block.Successors.All(next=>DeadUntilKilled(next,local,visiting,memo));
        visiting.Remove(block);memo[block]=result;return result;
    }
    static bool Reads(Instruction instruction,LocalVariable local)
    {
        var destinationIndex=instruction.OpCode==OpCode.Call?1:0;
        for(var n=0;n<instruction.Operands.Count;n++)
        {
            var operand=instruction.Operands[n];
            if(n==destinationIndex&&operand is LocalVariable&&ReferenceEquals(operand,instruction.Destination))continue;
            if(Contains(operand,local))return true;
        }
        return false;
    }
    static bool Contains(IOperand o,LocalVariable l)=>o switch {
        LocalVariable v=>ReferenceEquals(v,l),MemoryOperand m=>(m.Base!=null&&Contains(m.Base,l))||(m.Index!=null&&Contains(m.Index,l)),
        FieldReference f=>ReferenceEquals(f.Local,l)||f.Parent!=null&&Contains(f.Parent,l),AddressOf a=>Contains(a.Target,l),
        ArrayAccess a=>ReferenceEquals(a.Array,l)||Contains(a.Index,l),ArrayLength a=>ReferenceEquals(a.Array,l),_=>false};
    static bool AddressEscapes(IOperand o,LocalVariable l)=>o switch {
        AddressOf a=>Contains(a.Target,l),MemoryOperand m=>(m.Base!=null&&AddressEscapes(m.Base,l))||(m.Index!=null&&AddressEscapes(m.Index,l)),
        FieldReference f=>f.Parent!=null&&AddressEscapes(f.Parent,l),ArrayAccess a=>AddressEscapes(a.Index,l),_=>false};
}
