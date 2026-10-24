using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Recovers interface calls from GetInterfaceInvokeData which is usually inlined. that method scans klass->interfaceOffsets
// for the declaring interface, indexes the vtable with (entryOffset + slot), or falls back to a slow path
// helper when the scan fails.
public static class InterfaceDispatchRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        // offsets below are the 64-bit Il2CppClass layout
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return;

        var cfg = method.ControlFlowGraph!;
        // Opt-in local diagnostics only; do not change recovery or its gates.
        var trace=System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_INTERFACE_RVAS")?.Split(',')
            .Any(r=>string.Equals(r.Trim(),method.UnderlyingPointer.ToString("X"),System.StringComparison.OrdinalIgnoreCase))==true;
        if(trace)
        {
            System.Console.Error.WriteLine("INTERFACE BEFORE: "+method.FullName);
            foreach(var local in method.Locals)
                System.Console.Error.WriteLine("LOCAL "+local.Name+" TYPE "+local.Type?.FullName);
            foreach(var block in cfg.Blocks)
                System.Console.Error.WriteLine(block+"Successors: "+string.Join(",",block.Successors.Select(s=>s.ID)));
        }

        var definitions = new Dictionary<LocalVariable, Instruction>();
        var homeBlock = new Dictionary<Instruction, Block>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                homeBlock[instruction] = block;
                if (instruction.Destination is LocalVariable destination)
                    definitions[destination] = instruction;
            }
        }

        var changed = false;
        var matchedLookups=new List<(Instruction Dispatch,Match Lookup)>();

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var instruction in block.Instructions.ToList())
            {
                if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                    continue;

                if (MatchDispatch(method, instruction, definitions, homeBlock) is not { } match)
                {
                    if(trace) System.Console.Error.WriteLine("INTERFACE UNMATCHED: "+instruction);
                    continue;
                }

                if(trace) System.Console.Error.WriteLine($"INTERFACE MATCHED index={instruction.Index}: "+match.Resolved.FullName);

                RewriteDispatch(method, instruction, block, match, definitions);
                matchedLookups.Add((instruction,match));
                changed = true;
            }
        }

        // IL emission consumes explicit parameters only. For fully known,
        // non-generic managed calls, one trailing runtime MethodInfo is not a
        // C# argument and must not keep an unrelated lookup alive.
        var trimmedMetadata = false;
        foreach(var instruction in cfg.Blocks.SelectMany(b=>b.Instructions))
            if(instruction.Operands.Count>0 && (IsMatchedInvokeDataInfo(instruction.Operands[^1],definitions,
                matchedLookups.Select(m=>m.Lookup.InvokeDataPhi))
                || IsMatchedLookupMetadataPhi(instruction.Operands[^1],definitions,homeBlock,
                    matchedLookups.Select(m=>m.Lookup.InvokeDataPhi))
                || IsMatchedLookupMetadataPhi(instruction.Operands[^1],definitions,homeBlock,
                    matchedLookups.Select(m=>m.Lookup.InvokeDataPhi),
                    local=>method.Locals.Contains(local) && local.Type is null && !local.IsThis
                        && !local.IsReturn && !local.IsReturnBuffer && local.ParameterIndex<0)))
            {
                var trimmed = TrimIgnoredMethodInfo(instruction);
                changed |= trimmed;
                trimmedMetadata |= trimmed;
            }

        // Pruning a proven ignored operand makes its ordinary metadata phi
        // and +8 load dead. Use the existing all-use DCE proof before checking
        // lookup escape/deadness; do not exempt a still-live metadata consumer.
        if (trimmedMetadata) DeadCodeEliminator.Run(method);

        // A later proven dispatch can still carry stale raw argument-register
        // phis while we inspect an earlier lookup. Resolve ALL dispatches before
        // testing deadness; never ignore an unresolved call's uses.
        // Hidden MethodInfo register junk from an earlier lookup may be an
        // extra argument of a later slow lookup. Prove/remove later regions
        // first so earlier deadness sees the actual surviving graph. All
        // closed-region, side-effect and escape proofs remain mandatory.
        foreach(var (dispatch,lookup) in matchedLookups.AsEnumerable().Reverse())
            TryExciseLookup(cfg,lookup,definitions,homeBlock,
                trace ? gate=>System.Console.Error.WriteLine($"INTERFACE LOOKUP index={dispatch.Index} gate={gate}") : null);

        if (changed)
            DeadCodeEliminator.Run(method);

    }

    private const int InvokeDataShift = 4; // sizeof(VirtualInvokeData) == 16

    private record struct Match(
        MethodAnalysisContext Resolved,
        Instruction InvokeDataPhi,
        Block Merge,
        Instruction SlowCall,
        LocalVariable KlassLocal);

    private static Match? MatchDispatch(MethodAnalysisContext method, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        Match? Reject(string gate)
        {
            if (System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_INTERFACE_RVAS")?.Split(',')
                .Any(r=>string.Equals(r.Trim(),method.UnderlyingPointer.ToString("X"),System.StringComparison.OrdinalIgnoreCase))==true)
                System.Console.Error.WriteLine($"INTERFACE REJECT index={dispatch.Index} gate={gate}");
            return null;
        }
        // the call target loads VirtualInvokeData::methodPtr, separately or folded in
        var targetLoad = dispatch.Operands[0] switch
        {
            MemoryOperand folded => folded,
            LocalVariable target when Definition(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
            _ => default(MemoryOperand?)
        };

        if (targetLoad is not { Index: null, Scale: 0, Addend: 0, Base: LocalVariable invokeData })
            return Reject("invoke-data-load");

        if (Definition(definitions, invokeData) is not { OpCode: OpCode.Phi, Operands: [_, LocalVariable first, LocalVariable second] } phi)
            return Reject("invoke-data-phi");

        var firstDefinition = Definition(definitions, first);
        var secondDefinition = Definition(definitions, second);

        var slowCall = firstDefinition is { OpCode: OpCode.Call } 
            ? firstDefinition
            : secondDefinition is { OpCode: OpCode.Call } ? secondDefinition : null;
        var vtableEntry = ReferenceEquals(slowCall, firstDefinition) ? secondDefinition : firstDefinition;

        // slow path is GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot), never resolved
        if (slowCall is not { Operands: [Immediate, _, _, var interfaceArg, var slotArg, ..] })
            return Reject("slow-helper-call");

        if (ResolveDispatchOperand(interfaceArg, definitions) is not TypeAnalysisContext declaringInterface)
            return Reject("interface-metadata");

        if (declaringInterface is RuntimeMethodInfoAnalysisContext
            || !(declaringInterface is GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } || declaringInterface.IsInterface))
            return Reject("declaring-interface");

        if (ResolveDispatchOperand(slotArg, definitions) is not Immediate slotImmediate
            || slotImmediate.Value is < 0 or > ushort.MaxValue)
            return Reject("slot-immediate");

        var slot = (int)slotImmediate.Value;

        // fast path computes klass + vtableOffset + ((entryOffset + slot) << 4) (the +slot folds away for slot 0)
        if (MatchVTableEntryChain(definitions, vtableEntry, slot, RuntimeMetadataLayout.For(method).VTable) is not { } klassLocal)
            return Reject("vtable-chain");

        if (ResolveInterfaceSlot(declaringInterface, slot) is not { } resolved)
            return Reject("interface-slot-binding");

        if (!homeBlock.TryGetValue(phi, out var merge))
            return Reject("phi-owner-block");

        return new Match(resolved, phi, merge, slowCall, klassLocal);
    }

    private static LocalVariable? MatchVTableEntryChain(Dictionary<LocalVariable, Instruction> definitions, Instruction? vtableEntry, int slot, long vtableOffset)
    {
        // Native code also groups this as (klass + (index << 4)) + vtableOffset.
        // Keep both exact associations; never drop or guess the shift/offset.
        Instruction? groupedShift = null;
        if (vtableEntry is { OpCode: OpCode.Add, Operands: [_, LocalVariable inner, Immediate outerOffset] }
            && outerOffset.Value == vtableOffset)
        {
            vtableEntry = ChaseCopies(definitions, inner);
            if (vtableEntry is not { OpCode: OpCode.Add, Operands: [_, LocalVariable left, LocalVariable right] })
                return null;
            var shiftedSide = Definition(definitions, right) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 }] }
                ? left : right;
            groupedShift = ChaseCopies(definitions, shiftedSide);
        }

        if (vtableEntry is not { OpCode: OpCode.Add, Operands: [_, LocalVariable addLeft, LocalVariable addRight] })
            return null;

        var (klassCandidate, sum) = Definition(definitions, addRight) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 }] }
            ? (addRight, addLeft)
            : (addLeft, addRight);

        if (Definition(definitions, klassCandidate) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable }] })
            return null;

        if (groupedShift == null)
        {
            if (ChaseCopies(definitions, sum) is not { OpCode: OpCode.Add, Operands: [_, LocalVariable shifted, Immediate tableOffset] }
                || tableOffset.Value != vtableOffset)
                return null;
            groupedShift = ChaseCopies(definitions, shifted);
        }

        if (groupedShift is not { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable index, Immediate { Value: InvokeDataShift }] })
            return null;

        var entryOffset = ChaseCopies(definitions, index);

        // ADD Xn,Xn,Wm,UXTW #4 lifts as two exact integer conversions
        // followed by the scale above. Retain the low-word truncation contract;
        // do not treat an arbitrary cast, signed extension or addend as a copy.
        if (entryOffset is { OpCode: OpCode.NumericConvert,
                Operands: [_, TypeAnalysisContext { FullName: "System.UInt64" },
                    TypeAnalysisContext { FullName: "System.UInt32" }, LocalVariable narrowed] }
            && ChaseCopies(definitions, narrowed) is { OpCode: OpCode.NumericConvert,
                Operands: [_, TypeAnalysisContext { FullName: "System.UInt32" },
                    TypeAnalysisContext { FullName: "System.UInt32" }, LocalVariable beforeExtension] })
            entryOffset = ChaseCopies(definitions, beforeExtension);

        if (entryOffset is { OpCode: OpCode.Add, Operands: [_, LocalVariable beforeSlot, Immediate slotAddend] })
        {
            if (slotAddend.Value != slot)
                return null;

            entryOffset = ChaseCopies(definitions, beforeSlot);
        }
        else if (slot != 0)
            return null;

        if (entryOffset is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: not null }] })
            return null;

        return klassCandidate;
    }

    private static Instruction? Definition(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
        => definitions.TryGetValue(local, out var definition) ? definition : null;

    internal static IOperand? ResolveDispatchOperand(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        // MetadataResolver can replace the call argument itself, not just its
        // defining Move. Accept only the same exact metadata/immediate terminals.
        var visited = new HashSet<LocalVariable>();
        while (operand is LocalVariable local)
        {
            if (!visited.Add(local)) return null;
            var definition = Definition(definitions, local);
            if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                operand = source;
            // ARM64 MOV-immediate is also encoded as ORR with the zero register.
            // This pass runs before ConstantFolder; recognize only that exact
            // constant materialization, never infer metadata from arithmetic.
            else if (definition is { OpCode: OpCode.Or, NativeFloatingPointSize: 0,
                         Operands: [_, Immediate left, Immediate right] }
                     && (left.Value == 0 || right.Value == 0))
                operand = new Immediate(left.Value | right.Value);
            else return null;
        }
        return operand is TypeAnalysisContext or Immediate ? operand : null;
    }

    internal static bool TrimIgnoredMethodInfo(Instruction instruction)
    {
        if(instruction.OpCode is not (OpCode.Call or OpCode.CallVoid)
            || instruction.Operands[0] is not MethodAnalysisContext target
            || target.GenericParameters.Count!=0 || target.DeclaringType is null
            || target.DeclaringType.GenericParameters.Count!=0
            || target.DeclaringType is GenericInstanceTypeAnalysisContext
            || target is ConcreteGenericMethodAnalysisContext)return false;
        var explicitCount=(instruction.OpCode==OpCode.Call ? 2 : 1)
            +(target.IsStatic ? 0 : 1)+target.Parameters.Count;
        if(instruction.Operands.Count!=explicitCount+1)return false;
        // Never infer a signature from a raw register bank or trim missing args.
        if(target.AppContext.InstructionSet.CallingConventionResolver?.HasRawArgumentLayout(instruction,target.AppContext)==true)
            return false;
        var hidden=instruction.Operands[explicitCount];
        if(hidden is not (LocalVariable or RuntimeMethodInfoAnalysisContext)
            && hidden is not Immediate {Value:0})return false;
        instruction.RemoveOperandAt(explicitCount);
        return true;
    }

    internal static bool IsMatchedInvokeDataInfo(IOperand operand,Dictionary<LocalVariable,Instruction> definitions,
        IEnumerable<Instruction> matchedPhis)
    {
        // Do not globally strip metadata: other recovery passes use it even
        // when IL emission ignores it. Only a proven VirtualInvokeData+8 load
        // from THIS run's resolved interface lookup may be pruned here.
        return operand is LocalVariable local && Definition(definitions,local) is
            {OpCode:OpCode.Move,Operands:[_,MemoryOperand {Addend:8,Index:null,Scale:0,Base:LocalVariable pointer}]}
            && Definition(definitions,pointer) is {} phi && matchedPhis.Any(p=>ReferenceEquals(p,phi));
    }

    internal static bool IsMatchedLookupMetadataPhi(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homes,
        IEnumerable<Instruction> matchedPhis, System.Func<LocalVariable,bool>? ignoredNativeIncoming=null)
    {
        // The slow interface path may set a caller's hidden MethodInfo register
        // to zero. Later ordinary joins retain that phi as a trailing hidden
        // argument to a known NON-generic managed call, keeping the whole lookup
        // alive. Accept only incoming MethodInfo/zero leaves, with an actual phi
        // in THIS matched lookup's merge. Never globally trim arbitrary metadata.
        var matched = matchedPhis.ToArray();
        var merges = matched.Where(homes.ContainsKey).Select(p => homes[p]).ToHashSet();
        if (merges.Count == 0) return false;
        var path = new HashSet<LocalVariable>();
        var sawIncoming = false; var sawIgnoredIncoming = false; var sawZero = false;
        var sawMerge = false; var sawMatchedInfo = false; var budget = 256;
        bool Visit(IOperand value)
        {
            if (--budget < 0) return false;
            if (value is Immediate { Value: 0 }) { sawZero = true; return true; }
            if (value is not LocalVariable local) return false;
            if (!definitions.TryGetValue(local, out var definition))
            {
                sawIncoming |= local.IsMethodInfo;
                if(local.IsMethodInfo)return true;
                // Only the exact hidden operand of a known non-generic call
                // may opt in. Its OTHER phi leaf must be a full MethodInfo
                // load from THIS proven lookup; no arbitrary dead phi, zero
                // route, parameter, field read or foreign lookup qualifies.
                var ignored=ignoredNativeIncoming?.Invoke(local)==true;
                sawIgnoredIncoming |= ignored;
                return ignored;
            }
            // Another ordinary join can combine the caller's incoming metadata
            // with MethodInfo loaded from THIS already resolved dispatch. This
            // remains metadata even when the join is outside the lookup merge.
            // A raw pointer/read, foreign lookup or partial load proves nothing.
            if (definition is { OpCode: OpCode.Move, NativeReadSize: 8 }
                && IsMatchedInvokeDataInfo(local, definitions, matched))
            { sawMatchedInfo = true; return true; }
            if (!path.Add(local)) return false;
            try
            {
                if (definition is { OpCode: OpCode.Move, Operands: [_, var source] }) return Visit(source);
                if (definition.OpCode != OpCode.Phi || definition.Operands.Count < 3 || !homes.TryGetValue(definition, out var home)) return false;
                sawMerge |= merges.Contains(home);
                return definition.Operands.Skip(1).All(Visit);
            }
            finally { path.Remove(local); }
        }
        return Visit(operand) && (sawIgnoredIncoming ? sawMatchedInfo
            : sawIncoming && (sawMatchedInfo || sawZero && sawMerge));
    }

    private static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local))
        {
            if (Definition(definitions, local) is not { } definition)
                return null;

            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
            {
                local = source;
                continue;
            }

            return definition;
        }

        return null;
    }

    private static MethodAnalysisContext? ResolveInterfaceSlot(TypeAnalysisContext declaringInterface, int slot)
    {
        if (declaringInterface is GenericInstanceTypeAnalysisContext genericInstance)
        {
            var baseMethod = genericInstance.GenericType.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
            return baseMethod == null ? null : new ConcreteGenericMethodAnalysisContext(baseMethod, genericInstance.GenericArguments, []);
        }

        return declaringInterface.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
    }

    private static void RewriteDispatch(MethodAnalysisContext method, Instruction dispatch, Block block, Match match, Dictionary<LocalVariable, Instruction> definitions)
    {
        var resolved = match.Resolved;
        var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;
        var isTailCall = dispatch.OpCode == OpCode.IndirectJump;

        // an IndirectJump's return register operand is a stale use rather than a return slot, so rebuild from scratch
        if (isTailCall)
        {
            var operands = new List<IOperand> { resolved };

            if (!resolved.IsVoid)
                operands.Add(new LocalVariable("interfaceTailCallResult", callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax")));

            operands.AddRange(dispatch.Operands.Skip(2));
            dispatch.SetOperands(operands);
        }
        else
        {
            if (resolved.IsVoid)
                dispatch.RemoveOperandAt(1);

            dispatch.SetOperand(0, resolved);
        }

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.NativeVirtualDispatch = true;
        callingConventions?.RemapRawArguments(dispatch, resolved);

        // name [phi+8] as the hidden MethodInfo param, like ResolveVirtualCalls. A tail call's target
        // register doubles as an argument slot, so a stale [phi] load can turn up as an argument too,
        // and gets a placeholder so the VirtualInvokeData pointer still dies.
        var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
        for (var i = 1; i < dispatch.Operands.Count; i++)
        {
            if (dispatch.Operands[i] is not LocalVariable argument
                || Definition(definitions, argument) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable loadBase } load] }
                || !ReferenceEquals(Definition(definitions, loadBase), match.InvokeDataPhi))
                continue;

            if (load.Addend == 8 && assembly != null)
                dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            else if (load.Addend == 0)
                dispatch.SetOperand(i, new Immediate(0));
        }

        if (isTailCall)
        {
            var returnOperands = !method.IsVoid && !resolved.IsVoid
                ? new List<IOperand> { dispatch.Operands[1] }
                : [];

            block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            block.CalculateBlockType();
        }
    }

    // Bailing here is fine, it just leaves the (already resolved) call with dead lookup around it
    private static void TryExciseLookup(ISILControlFlowGraph cfg, Match match, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock,
        System.Action<string>? trace=null)
    {
        var merge = match.Merge;

        if (!homeBlock.TryGetValue(match.SlowCall, out var slowBlock))
        { trace?.Invoke("slow-block"); return; }

        if (Definition(definitions, match.KlassLocal) is not { } klassDefinition
            || !homeBlock.TryGetValue(klassDefinition, out var head) || head == merge)
        { trace?.Invoke("head-block"); return; }

        if (!TryFindLookupRegion(cfg, head, merge, match.SlowCall, out head, out var region))
        { trace?.Invoke("closed-pure-region"); return; }

        if (!MergePhisAreDead(cfg, merge, out var removable, trace))
        { trace?.Invoke("live-merge-phis"); return; }

        foreach (var instruction in removable)
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }

        foreach (var successor in head.Successors)
            successor.Predecessors.Remove(head);
        head.Successors.Clear();
        head.Successors.Add(merge);

        var terminator = head.Instructions[^1];
        if (terminator.OpCode is OpCode.Jump or OpCode.ConditionalJump)
        {
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(merge);
        }
        else
            head.AddInstruction(new Instruction(-1, OpCode.Jump, merge));

        head.CalculateBlockType();

        merge.Predecessors.RemoveAll(region.Contains);
        merge.Predecessors.Add(head);

        foreach (var block in region)
        {
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            foreach (var predecessor in block.Predecessors)
                predecessor.Successors.Remove(block);

            block.Successors.Clear();
            block.Predecessors.Clear();
            cfg.Blocks.Remove(block);
        }
    }

    // The klass pointer can be loaded BEFORE a source-level branch and reused
    // by several independent interface lookups. Its defining block is then
    // not this lookup's entry. Choose a smaller DOMINATING closed cut, keeping
    // every instruction in its entry block and every original escape/effect
    // check. Never consume the intervening business branch or its callbacks.
    internal static bool TryFindLookupRegion(ISILControlFlowGraph cfg, Block klassHead, Block merge,
        Instruction slowCall, out Block head, out HashSet<Block> region)
    {
        head=klassHead;region=[];
        var slowBlock=cfg.Blocks.SingleOrDefault(b=>b.Instructions.Contains(slowCall));
        if(slowBlock==null)return false;
        bool Proved(Block candidate,out HashSet<Block> found) =>
            TryCollectRegion(cfg,candidate,merge,out found) && found.Contains(slowBlock)
            && RegionIsSideEffectFree(found,slowCall) && !AnyValueEscapes(cfg,found,merge);
        if(Proved(klassHead,out region))return true;
        if(cfg.Blocks.Count>256)return false;
        var dominance=new DominatorInfo(cfg);
        if(!dominance.Dominates(klassHead,merge))return false;
        var visited=new HashSet<Block>();var current=merge;
        while(dominance.ImmediateDominators.TryGetValue(current,out var parent)
            && parent!=null && visited.Add(parent))
        {
            current=parent;
            if(ReferenceEquals(current,klassHead))break;
            if(!dominance.Dominates(klassHead,current) || current.Instructions.Count==0
                || current.Instructions[^1].OpCode is not (OpCode.Jump or OpCode.ConditionalJump))continue;
            if(Proved(current,out var found)){head=current;region=found;return true;}
        }
        region=[];return false;
    }

    // The region has to be closed, so nothing else may enter or leave it
    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block head, Block merge, out HashSet<Block> region)
    {
        region = [];

        var queue = new Queue<Block>(merge.Predecessors);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == head)
                continue;

            if (block == merge || block == cfg.EntryBlock || block == cfg.ExitBlock || region.Count > 64)
                return false;

            if (!region.Add(block))
                continue;

            foreach (var predecessor in block.Predecessors)
                queue.Enqueue(predecessor);
        }

        if (region.Count == 0)
            return false;

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(p => p != head && !collected.Contains(p)))
                return false;
            if (block.Successors.Any(s => s != merge && !collected.Contains(s)))
                return false;
        }

        // we rewrite the head's terminator, so it can't branch anywhere else
        return head.Successors.All(s => s == merge || collected.Contains(s));
    }

    private static bool RegionIsSideEffectFree(HashSet<Block> region, Instruction slowCall)
    {
        foreach (var block in region)
        {
            foreach (var instruction in block.Instructions)
            {
                if (ReferenceEquals(instruction, slowCall))
                    continue;

                var harmless = instruction.OpCode switch
                {
                    OpCode.Nop or OpCode.Jump or OpCode.ConditionalJump or OpCode.Phi => true,
                    OpCode.NumericConvert => instruction is { NativeFloatingPointSize: 0,
                        Operands: [LocalVariable, TypeAnalysisContext { FullName: "System.UInt32" or "System.UInt64" },
                            TypeAnalysisContext { FullName: "System.UInt32" }, LocalVariable] },
                    OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                        or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                        or OpCode.Not or OpCode.Negate
                        or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                        => instruction.Destination is LocalVariable,
                    _ => false,
                };

                if (!harmless)
                    return false;
            }
        }

        return true;
    }

    // Merge phis are exempt, their deadness gets checked separately
    private static bool AnyValueEscapes(ISILControlFlowGraph cfg, HashSet<Block> region, Block merge)
    {
        var regionDefs = new HashSet<LocalVariable>();
        foreach (var block in region)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    regionDefs.Add(destination);

        foreach (var block in cfg.Blocks)
        {
            if (region.Contains(block))
                continue;

            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Phi && block == merge)
                    continue;

                if (Uses(instruction, regionDefs))
                    return true;
            }
        }

        return false;
    }

    // They may only feed loads off the VirtualInvokeData pointer, which must themselves be dead
    private static bool MergePhisAreDead(ISILControlFlowGraph cfg, Block merge, out List<Instruction> removable,
        System.Action<string>? trace=null)
        => DeadPhiClosure(cfg.Blocks.SelectMany(b=>b.Instructions),
                          merge.Instructions.Where(i=>i.OpCode==OpCode.Phi),out removable,trace);

    internal static bool DeadPhiClosure(IEnumerable<Instruction> instructions, IEnumerable<Instruction> roots,
        out List<Instruction> removable, System.Action<string>? trace=null)
    {
        removable = [];
        var all=instructions.ToArray();
        var useSites = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in all)
        {
            foreach (var used in UsedLocals(instruction))
            {
                if (!useSites.TryGetValue(used, out var sites)) useSites[used] = sites = [];
                sites.Add(instruction);
            }
        }
        var definitions=all.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).ToDictionary(g=>g.Key,g=>g.Count());
        var queue=new Queue<Instruction>(roots);
        var proved=new HashSet<Instruction>();
        while (queue.TryDequeue(out var phi))
        {
            if (!proved.Add(phi))continue;
            if (phi.OpCode!=OpCode.Phi || phi.Destination is not LocalVariable phiDest
                || definitions.GetValueOrDefault(phiDest)!=1)
                return false;
            foreach (var use in useSites.TryGetValue(phiDest, out var phiUses) ? phiUses : [])
            {
                // Phi-only use chains and cycles are pure. Traverse ALL their
                // consumers; any real use aborts before anything is modified.
                if (use.OpCode==OpCode.Phi) { queue.Enqueue(use); continue; }
                if (use is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand] }
                    || (useSites.TryGetValue(loaded, out var loadUses) && loadUses.Count > 0))
                {
                    trace?.Invoke("phi-use:"+phiDest+":"+use);
                    if(use.Destination is LocalVariable result && useSites.TryGetValue(result,out var consumers))
                        foreach(var consumer in consumers)trace?.Invoke("loaded-use:"+result+":"+consumer);
                    return false;
                }
                proved.Add(use);
            }
        }
        removable=proved.ToList();
        return true;
    }

    private static bool Uses(Instruction instruction, HashSet<LocalVariable> candidates)
        => UsedLocals(instruction).Any(candidates.Contains);

    private static IEnumerable<LocalVariable> UsedLocals(Instruction instruction)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (instruction.Operands[i] is LocalVariable
                && ReferenceEquals(instruction.Operands[i], instruction.Destination))
                continue;

            foreach (var local in OperandLocals(instruction.Operands[i]))yield return local;
        }
    }

    private static IEnumerable<LocalVariable> OperandLocals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable local:yield return local;break;
            case AddressOf address:
                foreach(var local in OperandLocals(address.Target))yield return local;
                break;
            case MemoryOperand memory:
                if(memory.Base!=null)foreach(var local in OperandLocals(memory.Base))yield return local;
                if(memory.Index!=null)foreach(var local in OperandLocals(memory.Index))yield return local;
                break;
            case FieldReference field:
                yield return field.Local;
                if(field.Parent!=null)foreach(var local in OperandLocals(field.Parent))yield return local;
                break;
            case ArrayAccess access:
                yield return access.Array;
                foreach(var local in OperandLocals(access.Index))yield return local;
                break;
            case ArrayLength length:yield return length.Array;break;
        }
    }
}
