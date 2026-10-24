using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Post-SSA copy/constant cleanup. The bulk of copy and constant propagation is done earlier, in SSA,
/// by <see cref="SsaSimplifier"/>; this pass mops up the copies that <em>destroying</em> SSA leaves
/// behind - each phi is lowered to a <c>Move</c> on every incoming edge, so the phi's result becomes a
/// single local with one definition per predecessor.
///
/// Those multiple definitions mean a value is no longer single-assignment: at the join the definitions
/// merge, and which one reaches a use is path-dependent. So unlike <see cref="SsaSimplifier"/>, this
/// pass cannot blindly forward a definition - it walks the CFG and refuses to carry a multiply-defined
/// local's value across the join its other definitions merge at (where the phi used to be).
/// </summary>
public static class Simplifier
{
    public static void Simplify(MethodAnalysisContext method)
    {
        new SimplifierContext(method).Process();
    }

    private readonly ref struct SimplifierContext(MethodAnalysisContext method)
    {
        private readonly Dictionary<Block, Dictionary<Instruction, OperandList>> _sourceCache = [];
        private readonly MethodAnalysisContext _method = method;
        private readonly ISILControlFlowGraph _graph = method.ControlFlowGraph!;
        private readonly HashSet<LocalVariable> _mutableStructs = SsaSimplifier.MutableStructStorage(method.ControlFlowGraph!);

        public void Process()
        {
            PopulateSourceCache();

            InlineLocals();

            // Repeat until no change
            while (InlineConstantsSinglePass()) ;

            // More locals can now be inlined
            InlineLocals();

            _graph.RemoveNops();
            _graph.RemoveEmptyBlocks();
        }

        private void PopulateSourceCache()
        {
            #if NET5_0_OR_GREATER
            _sourceCache.EnsureCapacity(_graph.Blocks.Count);
            #endif

            foreach (var block in _graph.Blocks)
            {
                var sourceCache = new Dictionary<Instruction, OperandList>(block.Instructions.Count);
                foreach (var instruction in block.Instructions)
                {
                    sourceCache[instruction] = instruction.Sources;
                }

                _sourceCache[block] = sourceCache;
            }
        }

        private void UpdateSourceCache(Block block, Instruction instruction)
        {
            _sourceCache[block][instruction] = instruction.Operands;
        }

        private bool InlineConstantsSinglePass()
        {
            var changed = false;
            var definitionCounts = CountDefinitions();

            var visited = new HashSet<Block>();
            var queue = new Queue<Block>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            queue.Enqueue(_graph.EntryBlock);
            visited.Add(_graph.EntryBlock);

            while (queue.Count > 0)
            {
                var block = queue.Dequeue();

                for (var i = 0; i < block.Instructions.Count; i++)
                {
                    var instruction = block.Instructions[i];

                    // If it's move and it moves something to local, replace and remove it
                    if (instruction.OpCode == OpCode.Move && instruction.Operands[0] is LocalVariable local)
                    {
                        if (SsaSimplifier.PreserveStructCopy(local, instruction.Operands[1], _mutableStructs))
                            continue;
                        // These operands evaluate a load/check NOW. Substituting
                        // them at later uses re-reads mutable storage, duplicates
                        // checks, and moves exceptions across observable work.
                        // Preserve the snapshot; ordinary local copies still fold.
                        if (instruction.Operands[1] is MemoryOperand or FieldReference or ArrayAccess or ArrayLength
                            && !SingleImmediateLoadUse(block,i,local))
                            continue;
                        if (IsLocalUsedAfterInstruction(block, i + 1, local, out var usedByMemory))
                        {
                            // This can't be inlined into memory operand
                            if (usedByMemory) continue;

                            // A local with several definitions is not in SSA form, so its value at a join
                            // depends on the path taken; don't carry this definition across that join.
                            var stopAtJoins = definitionCounts.TryGetValue(local, out var defs) && defs > 1;

                            // Replace local
                            ReplaceLocalsUntilReassignment(block, i + 1, local, instruction.Operands[1], stopAtJoins,
                                instruction.NativeReadSize);

                            // Only drop the defining move once the local has no remaining uses; if the
                            // replacement stopped at a join, the local is still live past it so the move stays.
                            if (IsLocalUsedAfterInstruction(block, i + 1, local, out _))
                                continue;

                            // Change that move to nop
                            instruction.OpCode = OpCode.Nop;
                            instruction.SetOperands();
                            UpdateSourceCache(block, instruction);

                            changed = true;
                        }
                    }
                }

                foreach (var successor in block.Successors)
                {
                    if (visited.Add(successor))
                        queue.Enqueue(successor);
                }
            }

            return changed;
        }

        private bool SingleImmediateLoadUse(Block block,int index,LocalVariable local)
        {
            var next=block.Instructions.Skip(index+1).FirstOrDefault(i=>i.OpCode!=OpCode.Nop);
            if(next==null)return false;
            // Keep safe adjacent load/store and first-argument forwarding. No
            // read crosses an instruction, nor is it duplicated across uses.
            var permitted=next.OpCode==OpCode.Return && next.Operands.Count==1 && ReferenceEquals(next.Operands[0],local)
                || next.OpCode==OpCode.Move && next.Operands.Count==2 && ReferenceEquals(next.Operands[1],local)
                    && next.Operands[0] is LocalVariable or MemoryOperand or FieldReference
                || next.OpCode==OpCode.CallVoid && next.Operands.Count>1 && ReferenceEquals(next.Operands[1],local);
            if(!permitted)return false;
            var reads=0;
            foreach(var instruction in _graph.Instructions)
            for(var n=0;n<instruction.Operands.Count;n++)
            {
                if(instruction.Operands[n] is AddressOf {Target:LocalVariable addressed} && ReferenceEquals(addressed,local))
                    return false;
                var destinationIndex=instruction.OpCode is OpCode.Call or OpCode.IndirectCall ? 1 : 0;
                if(n==destinationIndex && ReferenceEquals(instruction.Destination,local))continue;
                if(ReadsLocal(instruction.Operands[n],local) && ++reads>1)return false;
            }
            return reads==1;
        }

        private static bool ReadsLocal(IOperand? operand,LocalVariable local,int depth=0)
        {
            if(depth>16)return true; // unknown/deep address trees cannot authorize forwarding
            return operand switch
            {
                LocalVariable value=>ReferenceEquals(value,local),
                MemoryOperand memory=>ReadsLocal(memory.Base,local,depth+1)||ReadsLocal(memory.Index,local,depth+1),
                FieldReference field=>ReferenceEquals(field.Local,local)||ReadsLocal(field.Parent,local,depth+1),
                ArrayAccess array=>ReferenceEquals(array.Array,local)||ReadsLocal(array.Index,local,depth+1),
                ArrayLength array=>ReferenceEquals(array.Array,local),
                AddressOf address=>ReadsLocal(address.Target,local,depth+1),
                _=>false
            };
        }

        private void InlineLocals()
        {
            var definitionCounts = CountDefinitions();

            var visited = new HashSet<Block>();
            var queue = new Queue<Block>(_method.ControlFlowGraph!.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            queue.Enqueue(_graph.EntryBlock);
            visited.Add(_graph.EntryBlock);

            while (queue.Count > 0)
            {
                var block = queue.Dequeue();

                for (var i = 0; i < block.Instructions.Count; i++)
                {
                    var instruction = block.Instructions[i];

                    // If it's move and it moves local to local, replace and remove it
                    if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable local, LocalVariable source] })
                    {
                        if (SsaSimplifier.PreserveStructCopy(local, source, _mutableStructs))
                            continue;
                        // A local with several definitions is not in SSA form, so its value at a join
                        // depends on the path taken; don't carry this definition across that join.
                        var stopAtJoins = definitionCounts.TryGetValue(local, out var defs) && defs > 1;

                        // Replace local with source
                        ReplaceLocalsUntilReassignment(block, i + 1, local, source, stopAtJoins);

                        // If the replacement stopped at a join merging another definition, the local is
                        // still live there - keep its defining move rather than dropping the value on this path.
                        if (IsLocalUsedAfterInstruction(block, i + 1, local, out _))
                            continue;

                        if (!_method.ParameterLocals.Contains(local))
                            _method.Locals.Remove(local);

                        // Change that move to nop
                        instruction.OpCode = OpCode.Nop;
                        instruction.SetOperands();
                        UpdateSourceCache(block, instruction);
                    }
                }

                foreach (var successor in block.Successors)
                {
                    if (visited.Add(successor))
                        queue.Enqueue(successor);
                }
            }
        }

        // Counts how many instructions define each local. A local with more than one definition is not in
        // SSA form: at a control-flow join its value depends on which predecessor was taken, so none of its
        // definitions may be propagated across that join - a phi would be needed there instead.
        private Dictionary<LocalVariable, int> CountDefinitions()
        {
            var counts = new Dictionary<LocalVariable, int>();

            foreach (var instruction in _graph.Blocks.SelectMany(block => block.Instructions))
            {
                if (instruction.Destination is LocalVariable local)
                    counts[local] = counts.TryGetValue(local, out var count) ? count + 1 : 1;
                // An escaped storage location is not single-assignment after
                // SSA destruction: the receiver of ref/out may be written by
                // the callee even without a Move destination in this graph.
                foreach (var operand in instruction.Operands)
                    if (operand is AddressOf { Target: LocalVariable addressed })
                        counts[addressed] = 2;
            }

            return counts;
        }

        private void ReplaceLocalsUntilReassignment(Block startBlock, int startIndex, LocalVariable local,
            IOperand replacement, bool stopAtJoins, int replacementReadSize = 0)
        {
            var visited = new HashSet<Block>();
            var remaining = new Stack<(Block, int)>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            visited.Add(startBlock);
            remaining.Push((startBlock, startIndex));

            while (remaining.Count > 0)
            {
                var (currentBlock, index) = remaining.Pop();

                // Process instructions starting at the given index
                for (var i = index; i < currentBlock.Instructions.Count; i++)
                {
                    var instruction = currentBlock.Instructions[i];

                    // Stop on this branch when reassigned
                    if (instruction.Destination is LocalVariable destLocal && destLocal == local)
                        return;

                    // Copies capture a value, not a live view of another local.
                    // Do not substitute a source after it has been overwritten,
                    // or either storage location's address has escaped.
                    if (replacement is LocalVariable replacementLocal
                        && ReferenceEquals(instruction.Destination, replacementLocal))
                        return;
                    if (instruction.Operands.Any(operand => operand is AddressOf { Target: LocalVariable addressed }
                        && (ReferenceEquals(addressed, local) || ReferenceEquals(addressed, replacement))))
                        return;

                    // Replace operands
                    for (var j = 0; j < instruction.Operands.Count; j++)
                    {
                        var operand = instruction.Operands[j];

                        if (operand is LocalVariable usedLocal && usedLocal == local)
                        {
                            if (replacement is MemoryOperand && instruction.OpCode == OpCode.Move && j == 1)
                            {
                                // A native load's width belongs to the copied
                                // value. Losing it at a store misidentifies a
                                // vector read as a scalar; guessing from the
                                // destination field's type is not safe.
                                if (instruction.NativeReadSize != 0 && instruction.NativeReadSize != replacementReadSize)
                                    continue;
                                instruction.NativeReadSize = replacementReadSize;
                            }
                            instruction.SetOperand(j, replacement);
                            UpdateSourceCache(currentBlock, instruction);
                        }

                        // A memory operand's base/index holds an address, so only a local replacement may
                        // be substituted there (copy propagation). A constant/value replacement is left in
                        // place - the caller sees the local is still used and keeps its defining move.
                        else if (operand is MemoryOperand memory && replacement is LocalVariable)
                        {
                            if (memory.Base is LocalVariable baseLocal && baseLocal == local)
                                memory.Base = replacement;

                            if (memory.Index is LocalVariable indexLocal && indexLocal == local)
                                memory.Index = replacement;

                            instruction.SetOperand(j, memory);
                            UpdateSourceCache(currentBlock, instruction);
                        }

                        // The object a field is accessed on is an address just like a memory base.
                        else if (operand is FieldReference field && replacement is LocalVariable fieldReplacement &&
                                 field.Local == local)
                        {
                            field.ReplaceLocal(local, fieldReplacement);
                        }
                    }
                }

                // Process successors
                foreach (var successor in currentBlock.Successors)
                {
                    // A join merges this local's other definitions, so for a non-SSA (multiply-defined)
                    // local the replacement must not flow past it - the value there is path-dependent.
                    if (stopAtJoins && successor.Predecessors.Count > 1)
                        continue;

                    if (visited.Add(successor))
                        remaining.Push((successor, 0));
                }
            }
        }

        private bool IsLocalUsedAfterInstruction(Block startBlock, int startIndex, LocalVariable local, out bool usedByMemory)
        {
            var visited = new HashSet<Block>();
            var remaining = new Stack<(Block, int)>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            visited.Add(startBlock);
            remaining.Push((startBlock, startIndex));

            usedByMemory = false;

            while (remaining.Count > 0)
            {
                var (currentBlock, index) = remaining.Pop();

                var blockSources = _sourceCache[currentBlock];

                // Process instructions
                for (var i = index; i < currentBlock.Instructions.Count; i++)
                {
                    var instruction = currentBlock.Instructions[i];
                    var sources = blockSources[instruction];

                    // Direct usage check
                    if (sources.Contains(local))
                        return true;

                    // A field access reads the object it is on, whether the field is being read or written,
                    // so the destination has to be considered too - a store is not in Sources.
                    foreach (var operand in instruction.Operands)
                    {
                        if (operand is FieldReference field && field.Local == local)
                        {
                            usedByMemory = true;
                            return true;
                        }

                        // Likewise, an array element or length reads the array, and taking a slot's address reads it
                        // however the callee uses it - none of which are in Sources when they sit in a destination position.
                        if (operand is ArrayAccess array && (array.Array == local || array.Index == local as IOperand))
                        {
                            usedByMemory = true;
                            return true;
                        }

                        if (operand is ArrayLength length && length.Array == local)
                        {
                            usedByMemory = true;
                            return true;
                        }

                        if (operand is AddressOf { Target: LocalVariable addressed } && addressed == local)
                        {
                            usedByMemory = true;
                            return true;
                        }
                    }

                    // Used in memory operand
                    foreach (var source in sources)
                    {
                        if (source is MemoryOperand memory)
                        {
                            if (memory.Base is LocalVariable memLocal && memLocal == local)
                            {
                                usedByMemory = true;
                                return true;
                            }

                            if (memory.Index is LocalVariable memLocal2 && memLocal2 == local)
                            {
                                usedByMemory = true;
                                return true;
                            }
                        }
                    }
                }

                // Process successors
                foreach (var successor in currentBlock.Successors)
                {
                    if (visited.Add(successor))
                        remaining.Push((successor, 0));
                }
            }

            return false;
        }
    }
}
