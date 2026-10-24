using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Original primary1359: this exact factory constructs the automatic default
// IndexOutOfRangeException. Only the immediately following SAME array access
// can replace its proven unsigned bounds predicate. Never delete a custom test.
public static class NativeArrayBoundsRecovery
{
    private const ulong Factory=0xAAE400;
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<bool>> Profiles=new();
    private static bool Supports(ApplicationAnalysisContext app)
        =>app.Binary.PointerSizeBytes==8 && app.UnityVersion.Major==2018 && app.UnityVersion.Minor==4
            && Profiles.GetValue(app,owner=>new Lazy<bool>(()=>
            {
                if(!CheckedUnboxRecovery.Supports(owner) || owner.Metadata.BaseStream is not MemoryStream stream
                    || !string.Equals(Convert.ToHexString(SHA256.HashData(stream.ToArray())),
                        "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",StringComparison.OrdinalIgnoreCase)
                    || !owner.Binary.TryMapVirtualAddressToRaw(Factory,out var raw)
                    || raw<0 || raw>owner.Binary.RawLength-56)return false;
                return string.Equals(Convert.ToHexString(SHA256.HashData(owner.Binary.GetRawBinaryContent().Slice((int)raw,56))),
                    "4bc67eb46897947e99a08b0bef6a3ba24890243f83401e89dea92ac96c86699b",StringComparison.OrdinalIgnoreCase);
            })).Value;

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} cfg
            || !cfg.Instructions.Any(i=>i.OpCode==OpCode.Newobj && i.NativeDirectCallTarget==Factory)
            || !Supports(method.AppContext))return 0;
        var count=0;
        foreach(var guard in cfg.Blocks.ToArray())
            if(TryRecover(method,guard,i=>i.NativeDirectCallTarget==Factory))count++;
        if(count>0){cfg.RemoveUnreachableBlocks();DeadCodeEliminator.Run(method);}
        return count;
    }

    private static bool Same(IOperand a,IOperand b)=>ReferenceEquals(a,b)
        || a is Immediate x && b is Immediate y && x.Value==y.Value;
    private static bool Bool(LocalVariable value)=>value.Type?.FullName=="System.Boolean";
    private static bool Index(IOperand value)=>value is Immediate {Value:>=0 and <=int.MaxValue}
        or LocalVariable {Type.FullName:"System.Int32" or "System.UInt32"};

    private static Instruction? Flag(IOperand operand,Dictionary<LocalVariable,Instruction> defs,
        Block guard,Instruction consumer,out bool invert)
    {
        invert=false;var seen=new HashSet<LocalVariable>();
        while(operand is LocalVariable local && Bool(local) && seen.Add(local) && defs.TryGetValue(local,out var definition))
        {
            var position=guard.Instructions.IndexOf(definition);
            if(position<0 || position>=guard.Instructions.IndexOf(consumer))return null;
            if(definition is {OpCode:OpCode.Not or OpCode.Move,Operands:[_,LocalVariable source]} && Bool(source))
            {if(definition.OpCode==OpCode.Not)invert=!invert;operand=source;consumer=definition;continue;}
            return definition;
        }
        return null;
    }

    private static bool Failure(ISILControlFlowGraph cfg,Block block,Block guard,Func<Instruction,bool> prove,
        out HashSet<Block> region,out LocalVariable? exception)
    {
        region=[block];exception=null;
        if(block.Predecessors.Count!=1 || !ReferenceEquals(block.Predecessors[0],guard))return false;
        var body=block.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(body.Length==0 || body[0] is not {OpCode:OpCode.Newobj,
            Operands:[LocalVariable created,TypeAnalysisContext {FullName:"System.IndexOutOfRangeException"}]} allocation
            || !prove(allocation))return false;
        exception=created;
        if(body.Length==2 && body[1] is {OpCode:OpCode.Throw,Operands:[var thrown]}
            && ReferenceEquals(thrown,created))return block.Successors.Count==1 && ReferenceEquals(block.Successors[0],cfg.ExitBlock);
        if(body.Length!=1 || block.Successors.Count!=1)return false;
        var transport=block.Successors[0];
        if(transport.Predecessors.Count!=1 || !ReferenceEquals(transport.Predecessors[0],block)
            || transport.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray() is not
                [Instruction {OpCode:OpCode.Throw,Operands:[var value]}]
            || !ReferenceEquals(value,created) || transport.Successors.Count!=1
            || !ReferenceEquals(transport.Successors[0],cfg.ExitBlock))return false;
        region.Add(transport);return true;
    }

    private static bool ManagedReference(TypeAnalysisContext? type)=>type is {IsValueType:false} && type.Type is
        LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_CLASS
        or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
        or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_STRING
        or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
        or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_ARRAY;

    private static bool ReferenceStore(MethodAnalysisContext method,ArrayAccess store,IOperand value)
    {
        if(store.Array.Type is not SzArrayTypeAnalysisContext array || !ManagedReference(array.ElementType))return false;
        // A null reference can never fail the covariance test, even for a
        // covariant runtime array. Unknown/generic value storage is excluded.
        if(value is Immediate {Value:0})return true;
        if(value is not LocalVariable source || !ManagedReference(source.Type)
            || !ReferenceEquals(array.ElementType,method.AppContext.SystemTypes.SystemObjectType))return false;
        var cfg=method.ControlFlowGraph!;
        var definitions=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,store.Array)).ToArray();
        if(definitions is not [Instruction {OpCode:OpCode.NewArr,
            Operands:[_,SzArrayTypeAnalysisContext allocated,_]}]
            || !ReferenceEquals(allocated.ElementType,method.AppContext.SystemTypes.SystemObjectType))return false;
        bool AddressEscapes(IOperand operand)=>operand switch {
            AddressOf address=>ForwardNullCheckRecovery.Uses(address.Target,store.Array),
            MemoryOperand memory=>(memory.Base!=null && AddressEscapes(memory.Base))
                || (memory.Index!=null && AddressEscapes(memory.Index)),
            FieldReference field=>field.Parent!=null && AddressEscapes(field.Parent),
            ArrayAccess access=>AddressEscapes(access.Index),_=>false};
        // Normal array element mutation cannot change the local's runtime
        // array type. Taking its address or passing it as a byref can.
        if(cfg.Instructions.Any(i=>i.Operands.Any(AddressEscapes)
            || i.IsCall && i.Operands.OfType<MethodAnalysisContext>().Any(m=>m.Parameters.Any(p=>p.ParameterType is ByRefTypeAnalysisContext))
                && i.Operands.Any(o=>ForwardNullCheckRecovery.Uses(o,store.Array))))return false;
        // The ordinary Stable proof below additionally requires this sole
        // NewArr definition to dominate every length producer.
        return true;
    }

    private static ArrayAccess? NextAccess(MethodAnalysisContext method,Block start)
    {
        var cfg=method.ControlFlowGraph!;
        var seen=new HashSet<Block>();var block=start;
        while(seen.Count<8 && seen.Add(block))
        {
            foreach(var instruction in block.Instructions)
            {
                if(instruction.OpCode==OpCode.Nop)continue;
                if(instruction.OpCode==OpCode.Jump && ReferenceEquals(instruction,block.Instructions.Last()))continue;
                if(instruction is {OpCode:OpCode.Return,Operands:[ArrayAccess returned]})return returned;
                // Native FCVTZS commonly materializes a scalar store value
                // before ldelema. This unchecked primitive conversion cannot
                // observe the array or throw; do not skip arbitrary producers.
                if(instruction is {OpCode:OpCode.NumericConvert,Operands:[LocalVariable converted,
                    TypeAnalysisContext to,TypeAnalysisContext from,LocalVariable input]}
                    && Scalar(to) && Scalar(from) && converted.Type is {} convertedType && input.Type is {} inputType
                    && NullBypassRuntimeCastRecovery.SameCastType(convertedType,to)
                    && NullBypassRuntimeCastRecovery.SameCastType(inputType,from))continue;
                if(instruction is not {OpCode:OpCode.Move,Operands:[var destination,var source]})return null;
                if(destination is LocalVariable && source is ArrayAccess load)return load;
                if(destination is LocalVariable && source is AddressOf {Target:ArrayAccess address}
                    && address.Array.Type is SzArrayTypeAnalysisContext {ElementType.IsValueType:true})return address;
                if(destination is ArrayAccess store && store.Array.Type is SzArrayTypeAnalysisContext storedArray
                    && (storedArray.ElementType.IsValueType || ReferenceStore(method,store,source))
                    && source is LocalVariable or Immediate or FloatLiteral or DoubleLiteral)return store;
                return null;
            }
            if(block.Successors.Count!=1 || block.Successors[0]==cfg.ExitBlock
                || block.Successors[0].Predecessors.Count!=1)return null;
            block=block.Successors[0];
        }
        return null;
    }

    private static bool Scalar(TypeAnalysisContext type)=>type.FullName is "System.Single" or "System.Double"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64";

    internal static bool TryRecover(MethodAnalysisContext method,Block guard,Func<Instruction,bool> prove)
    {
        var cfg=method.ControlFlowGraph!;
        if(guard.Successors.Count!=2 || guard.Successors.Distinct().Count()!=2
            || guard.Instructions.LastOrDefault() is not {OpCode:OpCode.ConditionalJump,
                Operands:[Block target,var condition]} branch || !guard.Successors.Contains(target))return false;
        var failures=new List<(Block Block,HashSet<Block> Region,LocalVariable Exception)>();
        foreach(var next in guard.Successors)
            if(Failure(cfg,next,guard,prove,out var region,out var exception))failures.Add((next,region,exception!));
        if(failures.Count!=1)return false;
        var failure=failures[0];var success=guard.Successors.Single(b=>!ReferenceEquals(b,failure.Block));
        if(success.Predecessors.Count!=1 || NextAccess(method,success) is not {} access
            || access.Array.Type is not SzArrayTypeAnalysisContext || !Index(access.Index))return false;
        if(cfg.Blocks.Where(b=>!failure.Region.Contains(b)).SelectMany(b=>b.Instructions).SelectMany(i=>i.Operands)
            .Any(o=>ForwardNullCheckRecovery.Uses(o,failure.Exception)))return false;
        var defs=cfg.Instructions.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var lengths=new HashSet<Instruction>();
        bool Length(IOperand operand,Instruction consumer)
        {
            if(operand is not LocalVariable local || local.Type?.FullName is not ("System.Int32" or "System.UInt32")
                || !defs.TryGetValue(local,out var definition) || !guard.Instructions.Contains(definition)
                || definition is not {OpCode:OpCode.Move,NativeReadSize:4,Operands:[_,ArrayLength length]}
                || !ReferenceEquals(length.Array,access.Array)
                || guard.Instructions.IndexOf(definition)>=guard.Instructions.IndexOf(consumer))return false;
            lengths.Add(definition);return true;
        }
        var comparison=Flag(condition,defs,guard,branch,out var invert);if(comparison==null)return false;
        bool? truePass=null;
        if(comparison.UnsignedComparison && comparison.Operands is [_,var left,var right])
        {
            if(Same(left,access.Index) && Length(right,comparison))truePass=comparison.OpCode switch {
                OpCode.CheckLess=>true,OpCode.CheckGreaterOrEqual=>false,_=>null};
            else if(Same(right,access.Index) && Length(left,comparison))truePass=comparison.OpCode switch {
                OpCode.CheckGreater=>true,OpCode.CheckLessOrEqual=>false,_=>null};
        }
        // For the literal first element, unsigned index >= length is exactly
        // length == 0. Do not apply this to index 1, signed tests or an unrelated
        // zero predicate. Both the 32-bit length producer and array remain bound.
        if(truePass==null && access.Index is Immediate {Value:0}
            && comparison.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
            && comparison.Operands is [_,var zeroLeft,var zeroRight]
            && (zeroRight is Immediate {Value:0} && Length(zeroLeft,comparison)
                || zeroLeft is Immediate {Value:0} && Length(zeroRight,comparison)))
            truePass=comparison.OpCode==OpCode.CheckNotEqual;
        if(truePass==null && comparison.OpCode==OpCode.And && comparison.Operands is [_,var a,var b])
        {
            bool Compound(IOperand lowerOperand,IOperand unequalOperand)
            {
                var lower=Flag(lowerOperand,defs,guard,comparison,out var lowerNot);
                var unequal=Flag(unequalOperand,defs,guard,comparison,out var unequalNot);
                if(!lowerNot || lower is not {OpCode:OpCode.CheckLess,UnsignedComparison:true,Operands:[_,var len,var index]}
                    || !Same(index,access.Index) || !Length(len,lower)
                    || unequal is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,
                        Operands:[_,LocalVariable difference,Immediate {Value:0}]}
                    || (unequal.OpCode==OpCode.CheckNotEqual)==unequalNot
                    || !defs.TryGetValue(difference,out var subtract)
                    || subtract is not {OpCode:OpCode.Subtract,NativeArithmeticSize:4,Operands:[_,var len2,var index2]}
                    || !Same(index2,access.Index) || !Length(len2,subtract))return false;
                return true;
            }
            if(Compound(a,b) || Compound(b,a))truePass=true;
        }
        if(truePass==null || ((truePass.Value!=invert)!=ReferenceEquals(target,success)) || lengths.Count==0)return false;
        bool Stable(LocalVariable local)
        {
            var writes=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,local)).ToArray();
            return method.ParameterLocals.Contains(local)?writes.Length==0
                :writes.Length==1 && lengths.All(length=>ForwardNullCheckRecovery.DefinitionDominates(cfg,writes[0],length));
        }
        if(!Stable(access.Array) || access.Index is LocalVariable indexLocal && !Stable(indexLocal))return false;
        var first=lengths.Min(i=>guard.Instructions.IndexOf(i));
        foreach(var operation in guard.Instructions.Skip(first))
        {
            if(ReferenceEquals(operation,branch) || lengths.Contains(operation) || operation.OpCode==OpCode.Nop)continue;
            if(operation.Destination is not LocalVariable destination || ReferenceEquals(destination,access.Array)
                || ReferenceEquals(destination,access.Index)
                || operation.OpCode is not (OpCode.Move or OpCode.Not or OpCode.And or OpCode.Subtract
                    or OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess or OpCode.CheckLessOrEqual
                    or OpCode.CheckGreater or OpCode.CheckGreaterOrEqual)
                || operation.Sources.Any(o=>o is not (LocalVariable or Immediate)))return false;
        }
        branch.OpCode=OpCode.Jump;branch.SetOperands(success);cfg.RemoveEdge(guard,failure.Block);guard.CalculateBlockType();
        DeadCodeEliminator.Run(cfg);
        // ArrayLength is normally effectful (it throws on null) and must not be
        // erased by generic DCE. Only here the proven next access supplies the
        // same null check before any observable effect. Keep any live length.
        foreach(var length in lengths)
            if(length.Destination is LocalVariable value && !cfg.Instructions.Any(i=>i!=length && i.OpCode!=OpCode.Nop
                && i.Sources.Any(o=>ForwardNullCheckRecovery.Uses(o,value))))
            {length.OpCode=OpCode.Nop;length.SetOperands();}
        return true;
    }
}
