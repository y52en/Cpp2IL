using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Remove null and bounds checks which are explicit in il2cpp but implicit in IL
public static class InjectedCheckRemover
{
    public static void Run(MethodAnalysisContext method)
    {
        if (System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_CHECK_RVA") is { } requested
            && string.Equals(requested, method.UnderlyingPointer.ToString("X"), System.StringComparison.OrdinalIgnoreCase))
        {
            System.Console.Error.WriteLine("Injected-check CFG before removal: " + method.FullName);
            foreach (var block in method.ControlFlowGraph!.Blocks)
                System.Console.Error.WriteLine(block + "Successors: " + string.Join(",", block.Successors.Select(s=>s.ID)));
        }
        Run(method.ControlFlowGraph!);
    }

    public static void Run(ISILControlFlowGraph cfg)
        => Run(cfg,false);

    public static void RunNullOnly(MethodAnalysisContext method)
    {
        if(method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            && method.AppContext.Binary.PointerSizeBytes==8 && method.AppContext.UnityVersion.Major==2018
            && method.AppContext.UnityVersion.Minor==4 && method.ControlFlowGraph is {} cfg)Run(cfg,true);
    }

    internal static void RunNullOnly(ISILControlFlowGraph cfg)=>Run(cfg,true);

    private static void Run(ISILControlFlowGraph cfg,bool nullOnly)
    {
        NormalizeThrowTerminators(cfg);
        var defOf = BuildDefMap(cfg);
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            if (block.BlockType != BlockType.TwoWay || block.Instructions.Count == 0)
                continue;

            var terminator = block.Instructions[^1];

            if (terminator.OpCode != OpCode.ConditionalJump)
                continue;

            if (terminator.Operands[0] is not Block target || block.Successors.Count != 2)
                continue;

            var fall = block.Successors.SingleOrDefault(s => !ReferenceEquals(s,target));
            if (fall == null) continue;
            var targetThrow = GetInjectedThrowType(target);
            var fallThrow = GetInjectedThrowType(fall);
            if ((targetThrow == null) == (fallThrow == null)) continue;
            var throwsWhenTrue = targetThrow != null;
            var thrownType = targetThrow ?? fallThrow!;
            if(nullOnly && thrownType!="System.NullReferenceException")continue;
            var throwing = throwsWhenTrue ? target : fall;
            var surviving = throwsWhenTrue ? fall : target;

            if (terminator.Operands[1] is not LocalVariable condition
                || !TryResolveCondition(condition, defOf, ref throwsWhenTrue, out var definition)
                || !IsInjectedCheck(definition, thrownType, throwsWhenTrue))
                continue;
            if (thrownType=="System.NullReferenceException")
            {
                var receiver=definition.Operands.Skip(1).OfType<LocalVariable>().SingleOrDefault();
                if(receiver==null)continue;
                if(!NextOperationRetainsNullThrow(cfg,surviving,receiver))
                {
                    if(receiver.Type is not SzArrayTypeAnalysisContext)continue;
                    // ldlen;pop preserves the original null exception HERE,
                    // without allocating a different explicit exception or
                    // delaying it past a checked conversion/application call.
                    // Empty arrays are valid: this is NOT a bounds check.
                    var index=checked(cfg.Instructions.Max(i=>i.Index)+1);
                    block.Instructions.Insert(block.Instructions.Count-1,new(index,OpCode.ArrayNullCheck,receiver));
                }
            }

            // Removing a fallthrough throw must still branch to the surviving
            // target; simply nopping the branch would execute the throw.
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(surviving);

            cfg.RemoveEdge(block, throwing);
            block.CalculateBlockType();
            removedAny = true;
        }

        if (!removedAny)
            return;

        // delete any throw blocks
        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(cfg);
    }

    // A later dereference is insufficient: a checked conversion, call, write
    // or return between the guard and that dereference changes which effect or
    // exception occurs first. Keep the original branch unless the very next
    // observable operation itself checks this same managed receiver.
    internal static bool NextOperationRetainsNullThrow(ISILControlFlowGraph cfg,Block start,LocalVariable receiver)
    {
        if(receiver.Type==null || receiver.Type.IsValueType || start.Predecessors.Count!=1)return false;
        if(ForwardNullCheckRecovery.TryPreserveNextManagedDereference(cfg,start,0,receiver))return true;
        var visited=new HashSet<Block>();var block=start;var budget=128;
        while(visited.Count<8 && visited.Add(block))
        {
            foreach(var instruction in block.Instructions)
            {
                if(--budget<0)return false;
                if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
                if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable destination,var source]})
                {
                    if(ReferenceEquals(destination,receiver))return false;
                    if(receiver.Type is SzArrayTypeAnalysisContext && source is ArrayLength length && ReferenceEquals(length.Array,receiver))return true;
                    if(receiver.Type is SzArrayTypeAnalysisContext && source is ArrayAccess access && ReferenceEquals(access.Array,receiver)
                        && access.Index is LocalVariable or Immediate)return true;
                    if(source is LocalVariable or Immediate)continue;
                }
                if(instruction.NativeVirtualDispatch && instruction.OpCode is OpCode.Call or OpCode.CallVoid
                    && instruction.Operands[0] is MethodAnalysisContext {IsStatic:false})
                {
                    var index=instruction.OpCode==OpCode.Call?2:1;
                    return instruction.Operands.Count>index && ReferenceEquals(instruction.Operands[index],receiver)
                        && instruction.Operands.Skip(index+1).All(o=>o is LocalVariable or Immediate);
                }
                return false;
            }
            if(block.Successors.Count!=1 || block.Successors[0]==cfg.ExitBlock)return false;
            block=block.Successors[0];
        }
        return false;
    }

    // Metadata recovery turns non-returning native exception helpers into Throw.
    // The native CFG was built earlier and may still contain a fallthrough edge
    // and instructions after the helper. Only code AFTER the throw is dead.
    private static void NormalizeThrowTerminators(ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks)
        {
            var index = block.Instructions.FindIndex(i => i.OpCode == OpCode.Throw);
            if (index < 0) continue;
            block.Instructions.RemoveRange(index + 1, block.Instructions.Count - index - 1);
            foreach (var successor in block.Successors.ToArray())
                cfg.RemoveEdge(block, successor);
            block.Successors.Clear();
            block.Successors.Add(cfg.ExitBlock);
            if (!cfg.ExitBlock.Predecessors.Contains(block)) cfg.ExitBlock.Predecessors.Add(block);
            block.CalculateBlockType();
        }
        cfg.RemoveUnreachableBlocks();
    }

    private static bool TryResolveCondition(LocalVariable condition,
        Dictionary<LocalVariable, Instruction> defs, ref bool throwsWhenTrue, out Instruction definition)
    {
        var visited = new HashSet<LocalVariable>();
        while (visited.Add(condition) && defs.TryGetValue(condition, out var current))
        {
            if (current.OpCode is OpCode.Not or OpCode.Move
                && current.Operands.Count == 2 && current.Operands[1] is LocalVariable source)
            {
                // Not also represents integer bitwise complement. Do not treat
                // an untyped or integer operation as a logical inversion.
                if (condition.Type?.FullName != "System.Boolean" || source.Type?.FullName != "System.Boolean")
                    break;
                if (current.OpCode == OpCode.Not) throwsWhenTrue = !throwsWhenTrue;
                condition = source;
                continue;
            }
            definition = current;
            return true;
        }
        definition = null!;
        return false;
    }

    private static bool IsInjectedCheck(Instruction definition, string thrownType, bool throwsWhenTrue) =>
        thrownType switch
        {
            "System.NullReferenceException" => definition.Operands.Count == 3
                && (definition.Operands[1] is Immediate { Value: 0 } || definition.Operands[2] is Immediate { Value: 0 })
                && (throwsWhenTrue ? definition.OpCode == OpCode.CheckEqual : definition.OpCode == OpCode.CheckNotEqual),
            "System.IndexOutOfRangeException" => throwsWhenTrue && definition.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual,
            _ => false
        };

    // The full name of the exception if this block does nothing but throw an injected check's exception, else null.
    private static string? GetInjectedThrowType(Block block)
    {
        string? thrown = null;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Nop or OpCode.Interrupt:
                case OpCode.Return when thrown != null:
                    continue;

                case OpCode.Throw when thrown == null
                    && instruction.Operands is [TypeAnalysisContext { FullName: "System.NullReferenceException" or "System.IndexOutOfRangeException" } exception]:
                    thrown = exception.FullName;
                    continue;

                default:
                    return null;
            }
        }

        return thrown;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                defs[local] = instruction;

        return defs;
    }
}
