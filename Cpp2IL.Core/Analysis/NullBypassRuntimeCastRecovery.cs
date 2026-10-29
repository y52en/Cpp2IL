using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Complete original GetUI<T> C: null -> result0 -> shared continuation;
// otherwise isinst, and ONLY the fingerprinted automatic InvalidCast transport
// on failure. Do not generalize an arbitrary as/throw or erase the null path.
public static class NullBypassRuntimeCastRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes!=8 || method.AppContext.UnityVersion.Major!=2018
            || method.AppContext.UnityVersion.Minor!=4 || method.ControlFlowGraph is not { } graph)return 0;
        var count=0;
        foreach(var block in graph.Blocks.ToArray())
            if(TryRecover(method,block,address=>InlineClassCastRecovery.IsMessageBuilder(method,address)))count++;
        if(count>0){graph.RemoveUnreachableBlocks();DeadCodeEliminator.Run(method);}
        return count;
    }

    internal static bool ReferenceType(TypeAnalysisContext type)
    {
        if(type is GenericParameterTypeAnalysisContext parameter)
        {
            if((parameter.Attributes&GenericParameterAttributes.NotNullableValueTypeConstraint)!=0)return false;
            return (parameter.Attributes&GenericParameterAttributes.ReferenceTypeConstraint)!=0
                || parameter.ConstraintTypes.Any(c=>c is not GenericParameterTypeAnalysisContext
                    && ReferenceType(c) && !c.IsInterface
                    && c.FullName is not ("System.Object" or "System.ValueType" or "System.Enum"));
        }
        return !type.IsValueType && type is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext
            or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext)
            && type.Type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                or Il2CppTypeEnum.IL2CPP_TYPE_STRING or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
                or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;
    }

    // SZArray contexts are constructed independently by signature and usage
    // resolution. Match their actual element identities, never full-name text.
    internal static bool SameCastType(TypeAnalysisContext left,TypeAnalysisContext right,int depth=0)
    {
        if(depth>16)return false;
        if(TrivialConstructorRecovery.SameType(left,right))return true;
        if(left is SzArrayTypeAnalysisContext a && right is SzArrayTypeAnalysisContext b)
            return SameCastType(a.ElementType,b.ElementType,depth+1);
        return left is GenericInstanceTypeAnalysisContext x && right is GenericInstanceTypeAnalysisContext y
            && ReferenceEquals(x.GenericType,y.GenericType) && x.GenericArguments.Count==y.GenericArguments.Count
            && x.GenericArguments.Zip(y.GenericArguments,(l,r)=>SameCastType(l,r,depth+1)).All(equal=>equal);
    }

    // A lowered return phi may also receive a value from unrelated application
    // branches. Preserve every such edge, copy and continuation instruction.
    // Only exact synthetic reference copies immediately before proven incoming
    // edges qualify. A write inside the continuation, a missing incoming value,
    // an unknown type or an escaped cast result is not this pattern.
    internal static bool ProvenContinuationCopies(Block success,Block guard,Block nullPath,
        LocalVariable? merged,LocalVariable output,TypeAnalysisContext target,
        Instruction[] writes,Instruction castCopy,Instruction zero)
    {
        var extra=success.Predecessors.Where(b=>!ReferenceEquals(b,guard) && !ReferenceEquals(b,nullPath)).ToArray();
        if(extra.Length==0)return writes.Length==2;
        if(merged==null || success.Predecessors.Distinct().Count()!=success.Predecessors.Count
            || writes.Length!=extra.Length+2)return false;
        foreach(var block in extra)
        {
            var body=block.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
            if(block.Successors.Count==1 && ReferenceEquals(block.Successors[0],success))
            {
                if(body.LastOrDefault() is {OpCode:OpCode.Jump,Operands:[var jump]})
                {if(!ReferenceEquals(jump,success))return false;body=body[..^1];}
            }
            else if(block.Successors.Count==2 && block.Successors.Distinct().Count()==2
                && block.Successors.Contains(success)
                && body.LastOrDefault() is {OpCode:OpCode.ConditionalJump,
                    Operands:[Block branch,LocalVariable {Type:{FullName:"System.Boolean"}}]}
                && block.Successors.Contains(branch))body=body[..^1];
            else return false;
            if(body.LastOrDefault() is not {Index:-1,OpCode:OpCode.Move,NativeWriteSize:0,
                Operands:[var destination,var value]} copy || !ReferenceEquals(destination,output)
                || !writes.Contains(copy) || ReferenceEquals(copy,castCopy) || ReferenceEquals(copy,zero))return false;
            if(value is not Immediate {Value:0}
                && (value is not LocalVariable {Type:{} type} local || ReferenceEquals(local,output)
                    || !ReferenceType(type) || !SameCastType(type,target)))return false;
            if(block.Instructions.Count(i=>ReferenceEquals(i.Destination,output))!=1)return false;
        }
        return writes.All(i=>ReferenceEquals(i,castCopy) || ReferenceEquals(i,zero)
            || extra.Any(b=>b.Instructions.Contains(i)));
    }

    internal static bool TryRecover(MethodAnalysisContext method,Block guard,Func<ulong,bool> helper)
    {
        var graph=method.ControlFlowGraph!;
        var check=guard.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        Instruction? mergeCopy=null;
        LocalVariable? merged=null;
        // Lowered phi: the non-null edge copies the isinst result to a
        // separate local, and the null edge writes zero to that SAME local.
        // Keep the copy; do not equate unrelated locals or erase a null path.
        if(check is [Instruction {OpCode:OpCode.IsInst,Operands:[LocalVariable castValue,..]},_,_,
                Instruction {OpCode:OpCode.Move,Operands:[LocalVariable mergeValue,LocalVariable copied]} copy,_]
            && ReferenceEquals(castValue,copied) && !ReferenceEquals(castValue,mergeValue))
        {
            mergeCopy=copy;merged=mergeValue;
            check=[check[0],check[1],check[2],check[4]];
        }
        if(check is not
            [Instruction {OpCode:OpCode.IsInst,Operands:[LocalVariable result,TypeAnalysisContext target,LocalVariable source]} cast,
             Instruction {OpCode:OpCode.CheckEqual,Operands:[LocalVariable flag,var tested,Immediate {Value:0}]},
             Instruction {OpCode:OpCode.Not,Operands:[LocalVariable nonnull,var inverted]},
             Instruction {OpCode:OpCode.ConditionalJump,Operands:[Block success,var condition]}]
            || !ReferenceEquals(tested,result) || !ReferenceEquals(inverted,flag) || !ReferenceEquals(condition,nonnull)
            || source.Type==null || !ReferenceType(source.Type) || !ReferenceType(target)
            || flag.Type?.FullName!="System.Boolean" || nonnull.Type?.FullName!="System.Boolean"
            || guard.Predecessors.Count!=1 || guard.Successors.Count!=2 || guard.Successors.Distinct().Count()!=2
            || !guard.Successors.Contains(success) || method.ParameterLocals.Contains(result))return false;
        if(merged!=null && (method.ParameterLocals.Contains(merged) || ReferenceEquals(merged,source)
            || merged.Type==null || !SameCastType(merged.Type,target)
            || graph.Blocks.Where(b=>!ReferenceEquals(b,guard)).SelectMany(b=>b.Instructions)
                .SelectMany(i=>i.Operands).Any(o=>RuntimeCheckedCastRecovery.Contains(o,result))))return false;
        var output=merged??result;
        var failure=guard.Successors.Single(b=>!ReferenceEquals(b,success));var before=guard.Predecessors[0];
        if(before.Successors.Count!=2 || before.Successors.Distinct().Count()!=2 || !before.Successors.Contains(guard)
            || before.Instructions.TakeLast(2).ToArray() is not
                [Instruction {OpCode:OpCode.CheckEqual,Operands:[LocalVariable nullFlag,var nullObject,Immediate {Value:0}]},
                 Instruction {OpCode:OpCode.ConditionalJump,Operands:[Block nullPath,var nullCondition]}]
            || !ReferenceEquals(nullObject,source) || !ReferenceEquals(nullCondition,nullFlag)
            || nullFlag.Type?.FullName!="System.Boolean" || ReferenceEquals(nullPath,guard)
            // The zero-result continuation may also be reached by an earlier
            // application failure (e.g. missing/empty assets). Its entire
            // body and ALL incoming edges remain unchanged by this rewrite.
            || !before.Successors.Contains(nullPath) || !nullPath.Predecessors.Contains(before)
            || nullPath.Successors.Count!=1
            || !ReferenceEquals(nullPath.Successors[0],success) || success.Predecessors.Count<2
            || !success.Predecessors.Contains(guard) || !success.Predecessors.Contains(nullPath)
            || !InlineClassTestRecovery.StableSource(method,source,guard))return false;
        var nullBody=nullPath.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(nullBody.Length==2 && nullBody[^1] is {OpCode:OpCode.Jump,Operands:[var exit]}
            && ReferenceEquals(exit,success))nullBody=nullBody[..^1];
        if(nullBody is not [Instruction {OpCode:OpCode.Move,Operands:[var nullResult,Immediate {Value:0}]} zero]
            || !ReferenceEquals(nullResult,output))return false;
        var resultWrites=graph.Instructions.Where(i=>ReferenceEquals(i.Destination,result)).ToArray();
        var outputWrites=graph.Instructions.Where(i=>ReferenceEquals(i.Destination,output)).ToArray();
        if(resultWrites.Length!=(merged==null?2:1) || !resultWrites.Contains(cast)
            || !outputWrites.Contains(mergeCopy??cast) || !outputWrites.Contains(zero)
            || !ProvenContinuationCopies(success,guard,nullPath,merged,output,target,outputWrites,mergeCopy??cast,zero)
            || graph.Instructions.Count(i=>ReferenceEquals(i.Destination,nullFlag))!=1
            || graph.Instructions.Count(i=>ReferenceEquals(i.Destination,flag))!=1
            || graph.Instructions.Count(i=>ReferenceEquals(i.Destination,nonnull))!=1
            || failure.Predecessors.Count!=1 || !ReferenceEquals(failure.Predecessors[0],guard))return false;
        var body=failure.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(body is not
            [Instruction {OpCode:OpCode.Move,NativeReadSize:8,Operands:[LocalVariable klass,MemoryOperand {Base:var obj,Index:null,Scale:0,Addend:0}]},
             Instruction {OpCode:OpCode.Move,NativeReadSize:8,Operands:[LocalVariable name,MemoryOperand {Base:var classBase,Index:null,Scale:0,Addend:0x40}]},
             Instruction {OpCode:OpCode.Call,Operands:[Immediate {Value:>=0} address,LocalVariable message,var fromClass,var toClass,..]},
             Instruction {OpCode:OpCode.Newobj,Operands:[LocalVariable exception,TypeAnalysisContext {FullName:"System.InvalidCastException"}]}]
            || !ReferenceEquals(obj,source) || !ReferenceEquals(classBase,klass) || !ReferenceEquals(fromClass,name)
            || !helper((ulong)address.Value) || failure.Successors.Count!=1)return false;
        var represented=toClass is RuntimeClassTypeAnalysisContext runtime?runtime.RepresentedType:toClass as TypeAnalysisContext;
        if(represented==null || !SameCastType(represented,target))return false;
        var transport=failure.Successors[0];
        if(transport.Predecessors.Count!=1 || !ReferenceEquals(transport.Predecessors[0],failure)
            || transport.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray() is not
                [Instruction {OpCode:OpCode.Throw,Operands:[var thrown]}]
            || !ReferenceEquals(thrown,exception) || transport.Successors.Count!=1
            || !ReferenceEquals(transport.Successors[0],graph.ExitBlock))return false;
        var removed=new[]{klass,name,message,exception,flag,nonnull};
        if(removed.Distinct().Count()!=removed.Length || removed.Contains(source) || removed.Contains(result)
            || graph.Blocks.Where(b=>!ReferenceEquals(b,guard) && !ReferenceEquals(b,failure) && !ReferenceEquals(b,transport))
                .SelectMany(b=>b.Instructions).SelectMany(i=>i.Operands)
                .Any(o=>removed.Any(v=>RuntimeCheckedCastRecovery.Contains(o,v))))return false;
        cast.OpCode=OpCode.CastClass;
        guard.Instructions=mergeCopy==null?[cast,new(check[^1].Index,OpCode.Jump,success)]
            :[cast,mergeCopy,new(check[^1].Index,OpCode.Jump,success)];
        graph.RemoveEdge(guard,failure);guard.CalculateBlockType();return true;
    }
}
