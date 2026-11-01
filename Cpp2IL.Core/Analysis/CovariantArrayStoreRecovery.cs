using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Do NOT turn a runtime array element class into a static isinst token.
// A proven following stelem.ref supplies the same runtime covariance check.
public static class CovariantArrayStoreRecovery
{
    private const string HelperHash = "93a0b8c8fe701340287e21b34675e26bfe4d03a475897d57d48e1560dc356e51";

    public static int Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.Binary.PointerSizeBytes != 8 || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return 0;
        try
        {
            var address = app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_is_inst;
            var offset = checked((int)app.Binary.MapVirtualAddressToRaw(address));
            var bytes = app.Binary.GetRawBinaryContent();
            if (offset < 0 || offset > bytes.Length - 0xf0) return 0;
            using var sha = SHA256.Create();
            if (string.Concat(sha.ComputeHash(bytes.Slice(offset, 0xf0).ToArray()).Select(b => b.ToString("x2"))) != HelperHash) return 0;
        }
        catch (Exception) { return 0; }
        var changes = 0;
        foreach (var guard in method.ControlFlowGraph!.Blocks.ToArray())
            if (TryRecover(method, guard)) changes++;
        if (changes != 0)
        {
            method.ControlFlowGraph.RemoveUnreachableBlocks();
            DeadCodeEliminator.Run(method);
        }
        return changes;
    }

    // Structural proof is separate from the native profile gate for unit tests.
    public static bool TryRecover(MethodAnalysisContext method, Block guard)
    {
        var cfg = method.ControlFlowGraph!;
        var defs = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var calls = guard.Instructions.Where(i => i.IsCall).ToArray();
        if (calls.Length != 1 || calls[0] is not { OpCode: OpCode.Call,
            Operands: [StringLiteral { Value: "il2cpp_vm_object_is_inst" }, LocalVariable result, var value,
                var elementClass, ..] } call
            || ResolveSnapshot(cfg,guard,call,elementClass,8) is not
                MemoryOperand { Base: LocalVariable klass, Addend: 0x40, Index: null }
            || value is not LocalVariable && value is not StringLiteral
                && value is not FieldReference { Field.FieldType: { IsValueType: false,
                    Type: Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_STRING
                        or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
                        or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST } }
            || !defs.TryGetValue(klass, out var klassDef)
            || klassDef is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable array, Addend: 0, Index: null }] }
            || array.Type is not SzArrayTypeAnalysisContext represented || represented.ElementType.IsValueType
            || klass.Type != null && (klass.Type is not RuntimeClassTypeAnalysisContext knownClass
                || !ReferenceEquals(knownClass.RepresentedType, represented))) return false;
        // ArrayRecovery can establish the allocation's SZArray type only after
        // the type fixpoint. Its exact unique [array+0] definition still proves
        // the runtime class load; do not guess a static element type or mutate
        // an unknown handle into a CIL isinst token. Contradictory known types
        // and multiply defined handles continue to fail closed.
        if (cfg.Instructions.Where(i => !guard.Instructions.Contains(i)).Any(i => i.Operands.Any(o =>
            !(o is LocalVariable && ReferenceEquals(o, i.Destination)) && Contains(o, result)))) return false;
        // Even a local copy can make the tested result escape via a second
        // variable. Only the exact null predicate may consume the result.
        if (guard.Instructions.Where(i => !ReferenceEquals(i, call)).Any(i => i.Operands.Any(o => Contains(o, result))
            && !(i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual && i.Operands is [_, var left, var right]
                && ((ReferenceEquals(left, result) && right is Immediate { Value: 0 })
                    || (ReferenceEquals(right, result) && left is Immediate { Value: 0 }))))) return false;
        if (guard.Instructions.Any(i => !ReferenceEquals(i, call) && i.OpCode != OpCode.Nop
            && !PureFlag(i) && !(i.OpCode == OpCode.Move && i.Destination is LocalVariable))) return false;
        var dependent = new HashSet<LocalVariable> { result };
        bool grew;
        do
        {
            grew = false;
            foreach (var i in guard.Instructions.Where(i => !ReferenceEquals(i, call)))
                if (i.Destination is LocalVariable destination
                    && i.Sources.Any(o => dependent.Any(local => Contains(o, local)))) grew |= dependent.Add(destination);
        } while (grew);
        if (cfg.Instructions.Where(i => !guard.Instructions.Contains(i)).Any(i => i.Operands.Any(o =>
            !(o is LocalVariable && ReferenceEquals(o, i.Destination)) && dependent.Any(local => Contains(o, local))))) return false;
        if (!Branch(cfg, guard, defs, result, out var success, out var failure)
            || !PlainThrow(cfg, failure, "System.ArrayTypeMismatchException") || failure.Predecessors.Count != 1) return false;

        var visited = new HashSet<Block>();
        IOperand? boundsIndex = null;
        Instruction? boundsComparison = null;
        var current = success;
        var found = false;
        while (visited.Add(current) && visited.Count <= 6)
        {
            foreach (var instruction in current.Instructions)
            {
                if (instruction.OpCode == OpCode.Nop) continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [ArrayAccess access, var stored] })
                {
                    if (!ReferenceEquals(access.Array, array) || !SameReferenceValue(stored, value)
                        || (boundsIndex != null && !SameIndex(access.Index, boundsIndex)
                            && !Word32ArrayIndexProof.SameIndex(method,boundsComparison,boundsIndex,access.Index,instruction))) return false;
                    found = true; break;
                }
                if (!PureFlag(instruction) && instruction.OpCode != OpCode.Jump
                    && !PureBoundsCalculation(instruction,array,cfg,current,defs)
                    && !Word32ArrayIndexProof.PureConversion(method,instruction)) return false;
            }
            if (found) break;
            if (current.Successors.Count == 1) { current = current.Successors[0]; continue; }
            if (boundsIndex != null || current.Successors.Count != 2
                || current.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block target, var condition] }) return false;
            var invert = false;
            var comparison = ResolveFlag(condition, defs, ref invert);
            IOperand index;
            bool passOnTarget;
            if (comparison is { OpCode: OpCode.CheckLess, Operands: [_, var testedIndex, var testedLength] }
                && ResolveSnapshot(cfg,current,comparison,testedLength,4) is ArrayLength length
                && ReferenceEquals(length.Array,array))
            { index=testedIndex; passOnTarget=!invert; }
            else if (comparison is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                    Operands: [_, var zeroLengthOperand, Immediate { Value: 0 }] }
                && ResolveSnapshot(cfg,current,comparison,zeroLengthOperand,4) is ArrayLength zeroLength
                && ReferenceEquals(zeroLength.Array,array))
            {
                // SZArray length is nonnegative. A constant-index-zero store
                // checks length != 0 without materializing 0 < length.
                index=new Immediate(0);
                passOnTarget=(comparison.OpCode==OpCode.CheckNotEqual)!=invert;
            }
            else if (TryCompoundBounds(comparison,defs,array,cfg,current,out var constantIndex))
            { index=new Immediate(constantIndex); passOnTarget=!invert; }
            else return false;
            var pass = passOnTarget ? target : current.Successors.Single(b => !ReferenceEquals(b, target));
            var fail = current.Successors.Single(b => !ReferenceEquals(b, pass));
            if (!PlainThrow(cfg, fail, "System.IndexOutOfRangeException")) return false;
            boundsIndex = index; boundsComparison = comparison; current = pass;
        }
        if (!found) return false;
        call.OpCode = OpCode.Nop; call.SetOperands();
        guard.Instructions.Last().OpCode = OpCode.Jump;
        guard.Instructions.Last().SetOperands(success);
        cfg.RemoveEdge(guard, failure); guard.CalculateBlockType();
        return true;
    }

    private static bool PureFlag(Instruction i) => i.OpCode is OpCode.Not or OpCode.ConditionalJump
        || i.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual;

    // Recognition only: retained loads are not substituted into the graph or
    // moved across effects. Only one same-block, exact-width definition before
    // its consumer can identify the snapshot's source.
    private static IOperand? ResolveSnapshot(ISILControlFlowGraph cfg,Block block,Instruction consumer,
        IOperand operand,int width)
    {
        if(operand is not LocalVariable snapshot)return operand;
        var definitions=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,snapshot)).ToArray();
        if(definitions.Length!=1 || definitions[0] is not
            {OpCode:OpCode.Move,Operands:[_,var source]} load || load.NativeReadSize!=width
            || !block.Instructions.Contains(load))return null;
        var start=block.Instructions.IndexOf(load);var end=block.Instructions.IndexOf(consumer);
        if(end<=start || block.Instructions.Skip(start+1).Take(end-start-1).Any(i=>i.IsCall)
            || cfg.Instructions.Any(i=>i.Operands.Any(o=>AddressEscapes(o,snapshot))))return null;
        return source;
    }

    private static bool AddressEscapes(IOperand operand,LocalVariable local) => operand switch
    {
        AddressOf address => Contains(address.Target,local),
        MemoryOperand memory => memory.Base!=null && AddressEscapes(memory.Base,local)
            || memory.Index!=null && AddressEscapes(memory.Index,local),
        ArrayAccess access => AddressEscapes(access.Index,local),
        FieldReference field => field.Parent!=null && AddressEscapes(field.Parent,local),
        _ => false
    };

    private static bool PureBoundsCalculation(Instruction instruction,LocalVariable array,
        ISILControlFlowGraph cfg,Block block,Dictionary<LocalVariable,Instruction> defs) => instruction switch
    {
        {OpCode:OpCode.Move,Operands:[LocalVariable snapshot,ArrayLength length],NativeReadSize:4}
            => ReferenceEquals(length.Array,array) && defs.TryGetValue(snapshot,out var definition)
                && ReferenceEquals(definition,instruction)
                && !cfg.Instructions.Any(i=>i.Operands.Any(o=>AddressEscapes(o,snapshot))),
        { OpCode: OpCode.Subtract, Operands: [LocalVariable { Type.FullName: "System.Int32" },
            var lengthOperand,Immediate { Value: >=0 and <=int.MaxValue }] }
            => ResolveSnapshot(cfg,block,instruction,lengthOperand,4) is ArrayLength length
                && ReferenceEquals(length.Array,array),
        { OpCode: OpCode.And, Operands: [LocalVariable { Type.FullName: "System.Boolean" },
            LocalVariable { Type.FullName: "System.Boolean" },LocalVariable { Type.FullName: "System.Boolean" }] } => true,
        _ => false
    };

    // ARM64 HI after CMP length,k is represented as (!C-borrow && !Z).
    // Require BOTH predicates and the identical array/constant: length>=k
    // and (length-k)!=0 imply length>k. Never accept a mere length!=k test.
    private static bool TryCompoundBounds(Instruction? comparison,Dictionary<LocalVariable,Instruction> defs,
        LocalVariable array,ISILControlFlowGraph cfg,Block block,out long index)
    {
        index=0;
        if(comparison is not { OpCode: OpCode.And, Operands: [_,var left,var right] })return false;
        return Match(left,right,out index) || Match(right,left,out index);
        bool Match(IOperand lowerOperand,IOperand unequalOperand,out long constant)
        {
            constant=0;
            var lowerInvert=false;var unequalInvert=false;
            var lower=ResolveFlag(lowerOperand,defs,ref lowerInvert);
            var unequal=ResolveFlag(unequalOperand,defs,ref unequalInvert);
            if(lower is not { OpCode: OpCode.CheckLess,Operands: [_,var lowerLengthOperand,
                    Immediate { Value: >=0 and <=int.MaxValue } bound] }
                || ResolveSnapshot(cfg,block,lower,lowerLengthOperand,4) is not ArrayLength lowerLength
                || !lowerInvert || !ReferenceEquals(lowerLength.Array,array)
                || unequal is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                    Operands: [_,LocalVariable difference,Immediate { Value: 0 }] }
                || (unequal.OpCode==OpCode.CheckNotEqual)==unequalInvert
                || !defs.TryGetValue(difference,out var subtraction)
                || subtraction is not { OpCode: OpCode.Subtract,
                    Operands: [_,var differenceLengthOperand,Immediate differenceBound] }
                || ResolveSnapshot(cfg,block,subtraction,differenceLengthOperand,4) is not ArrayLength differenceLength
                || !ReferenceEquals(differenceLength.Array,array) || differenceBound.Value!=bound.Value)return false;
            constant=bound.Value;return true;
        }
    }

    private static bool SameIndex(IOperand a,IOperand b) => ReferenceEquals(a,b)
        || a is Immediate left && b is Immediate right && left.Value==right.Value;

    private static bool SameReferenceValue(IOperand a,IOperand b) => ReferenceEquals(a,b) || (a,b) switch
    {
        (StringLiteral left,StringLiteral right) => left.Value==right.Value,
        (FieldReference left,FieldReference right) => ReferenceEquals(left.Field,right.Field)
            && ReferenceEquals(left.Local,right.Local) && left.Offset==right.Offset
            && (left.Parent==null && right.Parent==null || left.Parent!=null && right.Parent!=null
                && SameReferenceValue(left.Parent,right.Parent)),
        _ => false
    };

    private static Instruction? ResolveFlag(IOperand operand, Dictionary<LocalVariable, Instruction> defs, ref bool invert)
    {
        var seen = new HashSet<LocalVariable>();
        while (operand is LocalVariable local && seen.Add(local) && defs.TryGetValue(local, out var definition))
        {
            if (definition is { OpCode: OpCode.Not, Operands: [_, LocalVariable source] }
                && local.Type?.FullName == "System.Boolean" && source.Type?.FullName == "System.Boolean")
            { invert = !invert; operand = source; continue; }
            return definition;
        }
        return null;
    }

    private static bool Branch(ISILControlFlowGraph cfg, Block guard, Dictionary<LocalVariable, Instruction> defs,
        LocalVariable result, out Block success, out Block failure)
    {
        success = failure = cfg.ExitBlock;
        if (guard.Successors.Count != 2 || guard.Instructions.LastOrDefault() is not
            { OpCode: OpCode.ConditionalJump, Operands: [Block target, var condition] } || !guard.Successors.Contains(target)) return false;
        var invert = false;
        var comparison = ResolveFlag(condition, defs, ref invert);
        if (comparison?.Operands is not [_, var left, var right]
            || comparison.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
            || !((ReferenceEquals(left, result) && right is Immediate { Value: 0 })
                || (ReferenceEquals(right, result) && left is Immediate { Value: 0 }))) return false;
        var jumpsOnSuccess = (comparison.OpCode == OpCode.CheckNotEqual) != invert;
        success = jumpsOnSuccess ? target : guard.Successors.Single(b => !ReferenceEquals(b, target));
        var passing = success;
        failure = guard.Successors.Single(b => !ReferenceEquals(b, passing));
        return true;
    }

    private static bool Contains(IOperand operand, LocalVariable local) => ReferenceEquals(operand, local) || operand switch
    {
        MemoryOperand memory => (memory.Base != null && Contains(memory.Base, local)) || (memory.Index != null && Contains(memory.Index, local)),
        ArrayAccess access => ReferenceEquals(access.Array, local) || Contains(access.Index, local),
        ArrayLength length => ReferenceEquals(length.Array, local),
        FieldReference field => ReferenceEquals(field.Local, local),
        AddressOf address => Contains(address.Target, local),
        _ => false
    };

    private static bool PlainThrow(ISILControlFlowGraph cfg, Block block, string type)
    {
        var instructions = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        return block.Successors.Count == 1 && ReferenceEquals(block.Successors[0], cfg.ExitBlock)
            && instructions is [{ OpCode: OpCode.Newobj, Operands: [LocalVariable exception, TypeAnalysisContext owner] },
                { OpCode: OpCode.Throw, Operands: [var thrown] }]
            && owner.FullName == type && ReferenceEquals(exception, thrown);
    }
}
