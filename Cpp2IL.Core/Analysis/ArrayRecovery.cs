using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Turns the raw Il2CppArray layout (header, then length, then inline elements) back into array ops
public static class ArrayRecovery
{
    private static readonly HashSet<string> ArrayNewFunctions =
    [
        "SzArrayNew",
        "il2cpp_vm_array_new_specific",
        "il2cpp_array_new_specific",
    ];

    // Il2CppArray is {Il2CppObject obj; void* bounds; il2cpp_array_size_t max_length;} then the elements, on all versions(?)
    private static long LengthOffset(int pointerSize) => 3L * pointerSize;
    private static long ElementsOffset(int pointerSize) => 4L * pointerSize;

    // ARM commonly computes array + (index << log2(stride)) in separate ADDs.
    // Recover only proven memory loads/stores, never a pointer-valued load/LEA.
    public static bool RecoverSplitAccesses(MethodAnalysisContext method)
    {
        var cfg=method.ControlFlowGraph!;
        var definitions=SingleDefinitions(cfg);
        var pointerSize=method.AppContext.Binary.PointerSizeBytes;
        var changed=false;
        foreach(var instruction in cfg.Instructions)
        {
            if(instruction.OpCode!=OpCode.Move) continue;
            for(var slot=0;slot<2 && slot<instruction.Operands.Count;slot++)
            {
                var width=slot==0 ? instruction.NativeWriteSize : instruction.NativeReadSize;
                if(width<=0 || instruction.Operands[slot] is not MemoryOperand memory) continue;
                var terms=new Dictionary<LocalVariable,long>();long offset=memory.Addend;
                try
                {
                    if(!AccumulateAddress(memory.Base,1,terms,ref offset,definitions,0)
                        || !AccumulateAddress(memory.Index,Math.Max(memory.Scale,1),terms,ref offset,definitions,0)) continue;
                    var arrays=terms.Where(t=>t.Value!=0 && t.Key.Type is SzArrayTypeAnalysisContext).ToArray();
                    if(arrays.Length!=1 || arrays[0].Value!=1) continue;
                    var array=arrays[0].Key;
                    var indices=terms.Where(t=>t.Value!=0 && !ReferenceEquals(t.Key,array)).ToArray();
                    // Proven 32-bit length load (not LongLength, a store or a pointer).
                    if(slot==1 && width==4 && indices.Length==0 && offset==LengthOffset(pointerSize))
                    {
                        instruction.SetOperand(slot,new ArrayLength(array));changed=true;continue;
                    }
                    var stride=ElementSize(((SzArrayTypeAnalysisContext)array.Type!).ElementType,pointerSize);
                    if(stride<=0 || width!=stride) continue;
                    var delta=checked(offset-ElementsOffset(pointerSize));
                    IOperand index;
                    if(indices.Length==0 && delta>=0 && delta%stride==0) index=new Immediate(delta/stride);
                    else if(indices.Length==1 && indices[0].Value==stride && delta==0) index=indices[0].Key;
                    else continue;
                    instruction.SetOperand(slot,new ArrayAccess(array,index));changed=true;
                }
                catch(OverflowException) { /* Unprovable affine address: preserve diagnostics. */ }
            }
        }
        return changed;
    }

    private static bool AccumulateAddress(IOperand? operand,long factor,Dictionary<LocalVariable,long> terms,ref long offset,
        Dictionary<LocalVariable,Instruction?> definitions,int depth)
    {
        if(depth>12) return false;
        if(operand==null) return true;
        if(operand is Immediate immediate) { offset=checked(offset+checked(factor*immediate.Value));return true; }
        if(operand is not LocalVariable local) return false;
        if(definitions.TryGetValue(local,out var definition) && definition!=null)
        {
            // Preserve a proven 32-bit index computation as the index value.
            // Flattening (index+constant)<<scale into pointer bytes loses the
            // original integer wrap/sign boundary and makes delta nonzero.
            // Pointer-valued adds and unknown/mixed-width arithmetic still
            // follow the existing conservative address proof.
            if(local.Type?.FullName=="System.Int32"
                && definition is {OpCode:OpCode.Add or OpCode.Subtract,Operands:[_,var indexLeft,var indexRight]}
                && Int32IndexOperand(indexLeft) && Int32IndexOperand(indexRight))
            {
                terms[local]=checked(terms.GetValueOrDefault(local)+factor);
                return true;
            }
            if(definition is {OpCode:OpCode.Move,Operands:[_,LocalVariable copied]})
                return AccumulateAddress(copied,factor,terms,ref offset,definitions,depth+1);
            if(definition is {OpCode:OpCode.Add,Operands:[_,var left,var right]})
                return AccumulateAddress(left,factor,terms,ref offset,definitions,depth+1)
                    && AccumulateAddress(right,factor,terms,ref offset,definitions,depth+1);
            if(definition is {OpCode:OpCode.ShiftLeft,Operands:[_,var shifted,Immediate {Value:>=0 and <32} shift]})
                return AccumulateAddress(shifted,checked(factor*(1L<<(int)shift.Value)),terms,ref offset,definitions,depth+1);
            if(definition is {OpCode:OpCode.Multiply,Operands:[_,var multiplied,Immediate multiplier]})
                return AccumulateAddress(multiplied,checked(factor*multiplier.Value),terms,ref offset,definitions,depth+1);
        }
        // Do not follow memory loads, calls, phi values or multiply-defined locals
        // as though their pointer/numeric contents were an address expression.
        terms[local]=checked(terms.GetValueOrDefault(local)+factor);
        return true;
    }

    private static bool Int32IndexOperand(IOperand operand) => operand is
        LocalVariable {Type.FullName:"System.Int32"} or Immediate {Value:>=int.MinValue and <=int.MaxValue};

    // A pointer passed directly to a reviewed bulk copy is not a memory load.
    // Reuse the same affine address proof, keeping every typed word computation
    // atomic so its wrap/sign boundary cannot become pointer arithmetic.
    internal static ArrayAccess? MatchFullStructPointer(IOperand pointer,TypeAnalysisContext type,int pointerSize,
        Dictionary<LocalVariable,Instruction?> definitions)
    {
        var size=type is GenericInstanceTypeAnalysisContext
            ? ClosedGenericValueLayout.TryGet(type,pointerSize)?.Size??0
            : TypeSizes.UnboxedSize(type,pointerSize);
        if(size is <=0 or >4096)return null;
        var atomic=new Dictionary<LocalVariable,Instruction?>(definitions);
        foreach(var local in atomic.Keys.ToArray())
            if(local.Type?.FullName is "System.Int32" or "System.UInt32")atomic[local]=null;
        bool FullWidth(IOperand value,int depth=0)
        {
            if(depth>12)return false;
            if(value is Immediate)return true;
            if(value is not LocalVariable local)return false;
            if(local.Type is SzArrayTypeAnalysisContext || local.Type?.FullName is "System.Int32" or "System.UInt32")return true;
            if(!atomic.TryGetValue(local,out var definition)||definition==null)return false;
            if(definition is {OpCode:OpCode.Move,Operands:[_,LocalVariable source]})return FullWidth(source,depth+1);
            return definition.NativeArithmeticSize==8 && definition.OpCode is OpCode.Add or OpCode.Multiply or OpCode.ShiftLeft
                && definition.Operands.Skip(1).All(o=>FullWidth(o,depth+1));
        }
        if(!FullWidth(pointer))return null;
        var terms=new Dictionary<LocalVariable,long>();long offset=0;
        try
        {
            if(!AccumulateAddress(pointer,1,terms,ref offset,atomic,0))return null;
            var arrays=terms.Where(t=>t.Value!=0 && t.Key.Type is SzArrayTypeAnalysisContext).ToArray();
            if(arrays.Length!=1||arrays[0].Value!=1)return null;
            var array=arrays[0].Key;
            if(array.Type is not SzArrayTypeAnalysisContext {ElementType:var element}
                || !TrivialConstructorRecovery.SameType(element,type))return null;
            var indices=terms.Where(t=>t.Value!=0&&!ReferenceEquals(t.Key,array)).ToArray();
            var delta=checked(offset-ElementsOffset(pointerSize));
            if(indices.Length==0 && delta>=0 && delta%size==0 && delta/size<=int.MaxValue)
                return new(array,new Immediate(delta/size));
            if(indices.Length==1 && indices[0].Value==size && delta==0
                && indices[0].Key.Type?.FullName is "System.Int32" or "System.UInt32")
                return new(array,indices[0].Key);
        }
        catch(OverflowException){ /* A wrapped/unknown native address is not an array proof. */ }
        return null;
    }

    public static void Run(MethodAnalysisContext method)
    {
        RecoverSplitAccesses(method);
        RecoverStructComponents(method);
        RecoverAccesses(method);
        RecoverStructElementAddresses(method);
        GroupInitialisers(method.ControlFlowGraph!);
    }

    internal static void RecoverAllocationsOnly(MethodAnalysisContext method)
    {
        var definitions = method.ControlFlowGraph!.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is { OpCode: OpCode.Call, Operands: [StringLiteral { Value: var name }, LocalVariable, var typeOperand, _, ..] }
                && ArrayNewFunctions.Contains(name)
                && InterfaceDispatchRecovery.ResolveDispatchOperand(typeOperand, definitions) is SzArrayTypeAnalysisContext type)
                instruction.SetOperand(2, type);
            RecoverAllocation(instruction);
        }
    }

    // Later CFG/typing cleanup can make array-data pointers unambiguous. Do
    // not repeat unrestricted affine substitution over coalesced locals: only
    // a stable array + exact header, with the CURRENT direct index, is allowed.
    // The index is not expanded, retagged, moved or replaced with a prior value.
    public static int RecoverLateSplitLoads(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not { } graph)return 0;
        var definitions=graph.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).ToDictionary(g=>g.Key,g=>g.ToArray());
        DominatorInfo? dominance=null;var count=0;
        bool Before(Instruction definition,Instruction use)
        {
            var origins=graph.Blocks.Where(b=>b.Instructions.Contains(definition)).ToArray();
            var targets=graph.Blocks.Where(b=>b.Instructions.Contains(use)).ToArray();
            if(origins.Length!=1 || targets.Length!=1)return false;
            if(ReferenceEquals(origins[0],targets[0]))
                return origins[0].Instructions.IndexOf(definition)<origins[0].Instructions.IndexOf(use);
            if(graph.Blocks.Any(b=>b.Predecessors.Any(p=>!graph.Blocks.Contains(p))))return false;
            dominance??=new DominatorInfo(graph);
            return dominance.Dominates(origins[0],targets[0]);
        }
        foreach(var read in graph.Instructions.ToArray())
        {
            if(read is not {OpCode:OpCode.Move,Operands:[LocalVariable,
                    MemoryOperand {Base:LocalVariable address,Index:LocalVariable index,Addend:0} memory]}
                || !definitions.TryGetValue(address,out var addressDefinitions) || addressDefinitions.Length!=1
                || addressDefinitions[0] is not {OpCode:OpCode.Add,Operands:[_,LocalVariable array,Immediate offset]} definition
                || array.Type is not SzArrayTypeAnalysisContext arrayType
                || offset.Value!=ElementsOffset(method.AppContext.Binary.PointerSizeBytes)
                || index.Type is {IsValueType:false} or PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                || !Before(definition,read))continue;
            var stride=ElementSize(arrayType.ElementType,method.AppContext.Binary.PointerSizeBytes);
            if(stride<=0 || read.NativeReadSize!=stride || memory.Scale!=stride)continue;
            var writes=definitions.GetValueOrDefault(array,[]);
            if(method.ParameterLocals.Contains(array)?writes.Length!=0
                :writes.Length!=1 || !Before(writes[0],definition))continue;
            if(graph.Instructions.Any(i=>i.ImplicitDefinition is { } register
                && (register==address.Register || register==array.Register)))continue;
            read.SetOperand(1,new ArrayAccess(array,index));count++;
        }
        if(count>0)DeadCodeEliminator.Run(graph);
        return count;
    }

    // Lower exact component ranges into an existing managed array address and
    // field reference. No new operand kind: ldelema + ldfld/stfld preserves the
    // actual element storage instead of silently updating a value-type copy.
    public static bool RecoverStructComponents(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        if (pointerSize != 8) return false;
        var definitions = SingleDefinitions(cfg);
        var nextIndex = cfg.Instructions.Select(i => i.Index).DefaultIfEmpty(-1).Max() + 1;
        var changed = false;
        // This pass inserts fresh address locals and rewrites operands, but
        // never changes block edges or redefines an existing local. Reuse one
        // dominance snapshot; live same-block instruction order is still checked
        // after prefix insertion. Unknown/duplicated instruction homes decline.
        var blocks=cfg.Blocks.ToHashSet();
        var invalidPredecessors=cfg.Blocks.Any(b=>b.Predecessors.Any(p=>!blocks.Contains(p)));
        var homes=new Dictionary<Instruction,Block?>();
        foreach(var owner in cfg.Blocks)
        foreach(var item in owner.Instructions)
            if(!homes.TryAdd(item,owner) && !ReferenceEquals(homes[item],owner))homes[item]=null;
        DominatorInfo? dominance=null;
        bool DefinitionDominates(Instruction definition,Instruction use)
        {
            if(!homes.TryGetValue(definition,out var first) || first==null
                || !homes.TryGetValue(use,out var last) || last==null)return false;
            return ReferenceEquals(first,last)?first.Instructions.IndexOf(definition)<first.Instructions.IndexOf(use)
                :(dominance??=new DominatorInfo(cfg)).Dominates(first,last);
        }
        bool StableFullWidthTerm(LocalVariable value,Instruction use)
        {
            if(invalidPredecessors)return false;
            return method.ParameterLocals.Contains(value)?!definitions.ContainsKey(value)
                :definitions.TryGetValue(value,out var write) && write!=null && DefinitionDominates(write,use);
        }
        bool FullWidthAddressStable(IOperand? value,Instruction use,int depth=0)
        {
            if(depth>12)return false;
            if(value==null || value is Immediate)return true;
            if(value is not LocalVariable local)return false;
            if(method.ParameterLocals.Contains(local))return !definitions.ContainsKey(local);
            if(!definitions.TryGetValue(local,out var definition) || definition==null
                || !DefinitionDominates(definition,use))return false;
            // This matches AccumulateAddress: a typed Int32 add/sub is a
            // snapshot index, not a pointer expression to expand further.
            if(local.Type?.FullName=="System.Int32"
                && definition is {OpCode:OpCode.Add or OpCode.Subtract,Operands:[_,var left,var right]}
                && Int32IndexOperand(left) && Int32IndexOperand(right))return true;
            if(definition is {OpCode:OpCode.Move,Operands:[_,LocalVariable source]})return FullWidthAddressStable(source,definition,depth+1);
            if(definition.OpCode is OpCode.Add or OpCode.ShiftLeft or OpCode.Multiply)
                return definition.Operands.Skip(1).All(o=>FullWidthAddressStable(o,definition,depth+1));
            return local.Type!=null;
        }
        TypeAnalysisContext? MaterializedType(IOperand value)=>value switch {
            LocalVariable local=>local.Type,
            FloatLiteral=>method.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral=>method.AppContext.SystemTypes.SystemDoubleType,
            FieldReference {Parent:null} field when !field.Field.IsStatic && field.Offset==field.Field.Offset
                && field.Local.Type?.IsValueType==true=>field.Field.FieldType,
            _=>null};
        foreach (var block in cfg.Blocks)
        foreach (var instruction in block.Instructions.ToArray())
        {
            if (instruction is not { OpCode: OpCode.Move, Operands.Count: 2 }) continue;
            var prefixes = new List<Instruction>();
            for (var slot = 0; slot < 2; slot++)
            {
                var width = slot == 0 ? instruction.NativeWriteSize : instruction.NativeReadSize;
                if (width <= 0 || instruction.Operands[slot] is not MemoryOperand memory) continue;
                try
                {
                    var terms = new Dictionary<LocalVariable, long>();
                    long offset = memory.Addend;
                    if (!AccumulateAddress(memory.Base, 1, terms, ref offset, definitions, 0)
                        || !AccumulateAddress(memory.Index, Math.Max(memory.Scale, 1), terms, ref offset, definitions, 0)) continue;
                    var arrays = terms.Where(t => t.Value != 0 && t.Key.Type is SzArrayTypeAnalysisContext).ToArray();
                    if (arrays.Length != 1 || arrays[0].Value != 1) continue;
                    var array = arrays[0].Key;
                    var element = ((SzArrayTypeAnalysisContext)array.Type!).ElementType;
                    if (!element.IsValueType || element.HasAnyGenericParameters() || ElementSize(element, pointerSize) != 0) continue;
                    var stride = MetadataElementSize(element, pointerSize);
                    var delta = checked(offset - ElementsOffset(pointerSize));
                    if (stride <= 0 || stride > int.MaxValue || delta < 0) continue;
                    var indices = terms.Where(t => t.Value != 0 && !ReferenceEquals(t.Key, array)).ToArray();
                    IOperand index;
                    long component;
                    if (indices.Length == 0)
                    {
                        index = new Immediate(delta / stride);
                        component = delta % stride;
                    }
                    else if (indices.Length == 1 && indices[0].Value == stride && delta < stride)
                    {
                        index = indices[0].Key;
                        component = delta;
                    }
                    else continue;
                    if (width > stride || component > stride - width) continue;
                    if(width==stride)
                    {
                        // A real native whole-width scalar/vector transfer can
                        // be either a typed whole element, or the sole scalar
                        // field of a wrapper. Never guess from the width alone.
                        if(width is not (1 or 2 or 4 or 8 or 16)
                            || terms.Where(t=>t.Value!=0).Any(t=>!StableFullWidthTerm(t.Key,instruction))
                            || !FullWidthAddressStable(memory.Base,instruction)
                            || !FullWidthAddressStable(memory.Index,instruction))continue;
                        var value=instruction.Operands[slot==0?1:0];
                        if(slot==1 && value is not LocalVariable)continue;
                        var fullValueType=MaterializedType(value);
                        if(fullValueType==null)continue;
                        if(TrivialConstructorRecovery.SameType(fullValueType,element))
                        {
                            instruction.SetOperand(slot,new ArrayAccess(array,index));changed=true;continue;
                        }
                        var fields=element.Fields.Where(f=>!f.IsStatic
                            && (f.Attributes&System.Reflection.FieldAttributes.Literal)==0).ToArray();
                        if(fields.Length!=1 || fields[0].Offset!=0 || component!=0
                            || ElementSize(fields[0].FieldType,pointerSize)!=width
                            || !TrivialConstructorRecovery.SameType(fullValueType,fields[0].FieldType))continue;
                    }
                    var name = "arrayElementAddress" + nextIndex;
                    var address = new LocalVariable(name, new Register(null, name), new ByRefTypeAnalysisContext(element));
                    var field = NestedFieldAccess.Find(element, address, component, width);
                    if (field == null) continue;
                    if (slot == 1 && instruction.Operands[0] is FieldReference targetField
                        && targetField.Field.FieldType.FullName != field.Field.FieldType.FullName) continue;
                    if (slot == 1 && instruction.Operands[0] is LocalVariable { Type: { } known }
                        && known.FullName != field.Field.FieldType.FullName) continue;
                    var prefix = new Instruction(nextIndex++, OpCode.Move, address, new AddressOf(new ArrayAccess(array, index)));
                    prefixes.Add(prefix);
                    method.Locals.Add(address);
                    instruction.SetOperand(slot, field);
                    if (slot == 1 && instruction.Operands[0] is LocalVariable loaded && loaded.Type == null)
                        loaded.Type = field.Field.FieldType;
                    changed = true;
                }
                catch (OverflowException) { /* Keep unprovable native ranges as diagnostics. */ }
            }
            if (prefixes.Count == 0) continue;
            block.Instructions.InsertRange(block.Instructions.IndexOf(instruction), prefixes);
            // Usually branches name blocks, but retain correct entry semantics
            // for graphs whose jump operands directly name an instruction.
            foreach (var branch in cfg.Instructions)
            for (var slot = 0; slot < branch.Operands.Count; slot++)
                if (ReferenceEquals(branch.Operands[slot], instruction)) branch.SetOperand(slot, prefixes[0]);
        }
        return changed;
    }

    private static void RecoverAccesses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            RecoverAllocation(instruction);

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand memory
                    || memory.Base is not LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array)
                    continue;

                if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
                {
                    instruction.SetOperand(i, new ArrayLength(array));
                    continue;
                }

                if (ElementIndex(memory, arrayType, pointerSize) is { } index)
                    instruction.SetOperand(i, new ArrayAccess(array, index));
            }
        }
    }

    // Group initializers after an array allocation together so ILSpy decompiles them better
    private static void GroupInitialisers(ISILControlFlowGraph cfg)
    {
        var movedAny = false;

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var allocation in block.Instructions.ToList())
            {
                if (allocation.OpCode != OpCode.NewArr || allocation.Operands[0] is not LocalVariable array)
                    continue;

                var stores = new List<(Block Block, Instruction Instruction)>();
                var current = block;
                var index = current.Instructions.IndexOf(allocation) + 1;

                while (true)
                {
                    if (index >= current.Instructions.Count)
                    {
                        // only a straight-line run can be regrouped without changing what runs when
                        if (current.Successors.Count != 1 || current.Successors[0].Predecessors.Count != 1)
                            break;

                        current = current.Successors[0];
                        index = 0;
                        continue;
                    }

                    var instruction = current.Instructions[index];

                    if (IsElementStore(instruction, array))
                    {
                        stores.Add((current, instruction));
                        index++;
                        continue;
                    }

                    if (!ReadsArray(instruction, array))
                    {
                        index++;
                        continue;
                    }

                    // Found the first read. Move the allocation and its stores immediately in front, so the whole array is built in one chain with the elements already computed.
                    if (stores.Count > 1)
                    {
                        foreach (var (storeBlock, store) in stores)
                            storeBlock.Instructions.Remove(store);

                        block.Instructions.Remove(allocation);

                        var moved = new List<Instruction> { allocation };
                        moved.AddRange(stores.Select(s => s.Instruction));

                        current.Instructions.InsertRange(current.Instructions.IndexOf(instruction), moved);
                        movedAny = true;
                    }

                    break;
                }
            }
        }

        // Emptying a block out entirely leaves branches pointing at nothing to jump to
        if (movedAny)
            cfg.RemoveEmptyBlocks();
    }

    private static bool IsElementStore(Instruction instruction, LocalVariable array) =>
        instruction.OpCode == OpCode.Move && instruction.Operands[0] is ArrayAccess { Index: Immediate } stored
                                          && ReferenceEquals(stored.Array, array)
                                          && !ReadsArray(instruction, array);

    private static bool ReadsArray(Instruction instruction, LocalVariable array)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (i == 0 && instruction.OpCode == OpCode.Move)
                continue;

            var reads = instruction.Operands[i] switch
            {
                LocalVariable local => ReferenceEquals(local, array),
                ArrayAccess access => ReferenceEquals(access.Array, array),
                ArrayLength length => ReferenceEquals(length.Array, array),
                MemoryOperand memory => ReferenceEquals(memory.Base, array) || ReferenceEquals(memory.Index, array),
                AddressOf { Target: LocalVariable addressed } => ReferenceEquals(addressed, array),
                _ => false
            };

            if (reads)
                return true;
        }

        return false;
    }

    private static void RecoverAllocation(Instruction instruction)
    {
        // Call "SzArrayNew", result, typeof(T[]), length, ...
        if (!instruction.IsCall || instruction.Operands is not [StringLiteral { Value: var name }, LocalVariable result, TypeAnalysisContext type, { } length, ..]
            || !ArrayNewFunctions.Contains(name))
            return;

        instruction.OpCode = OpCode.NewArr;
        instruction.SetOperands(result, type, length);

        if (result.Type is not SzArrayTypeAnalysisContext)
            result.Type = type;
    }

    private static IOperand? ElementIndex(MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, int pointerSize)
    {
        var elementSize = ElementSize(arrayType.ElementType, pointerSize);
        var offset = memory.Addend - ElementsOffset(pointerSize);

        if (offset < 0 || elementSize == 0 || offset % elementSize != 0)
            return null;

        if (memory.Index == null)
            return memory.Scale == 0 ? new Immediate(offset / elementSize) : null;

        return memory.Scale == elementSize && offset == 0 ? memory.Index : null;
    }

    private static long ElementSize(TypeAnalysisContext elementType, int pointerSize)
    {
        if (!elementType.IsValueType)
            return pointerSize;

        return elementType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Int16" or "System.UInt16" or "System.Char" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" => 8,
            "System.IntPtr" or "System.UIntPtr" => pointerSize,
            _ => 0 // struct arrays are handled by the element-address path, which sizes them from metadata
        };
    }

    // Recovers &array[i] over struct arrays. Struct elements are never loaded outright, the compiler
    // computes their address via lea chains and calls through it. We solve the index as a linear function
    // of a local and demand an exact hit on the metadata stride, so a real load can't match by accident.
    private static void RecoverStructElementAddresses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var cfg = method.ControlFlowGraph!;

        var definitions = SingleDefinitions(cfg);
        var uses = CollectUses(cfg);

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.IsCall)
            {
                for (var i = 1; i < instruction.Operands.Count; i++)
                {
                    if (MatchElementAddress(instruction.Operands[i], pointerSize, definitions) is { } inlined)
                        instruction.SetOperand(i, inlined);
                }

                continue;
            }

            // a Move from memory could be a load or a lifted lea, and only the uses tell them apart
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand] })
                continue;

            if (definitions.TryGetValue(destination, out var single) && single == null)
                continue;

            if (!uses.TryGetValue(destination, out var destinationUses) || destinationUses.Count == 0
                || !destinationUses.All(u => u.Instruction.IsCall || IsMemoryBase(u.Instruction.Operands[u.OperandIndex], destination)))
                continue;

            if (MatchElementAddress(instruction.Operands[1], pointerSize, definitions) is { } address)
                instruction.SetOperand(1, address);
        }
    }

    private static AddressOf? MatchElementAddress(IOperand operand, int pointerSize, Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (operand is not MemoryOperand memory
            || memory.Base is not LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array)
            return null;

        var elementType = arrayType.ElementType;
        if (!elementType.IsValueType || ElementSize(elementType, pointerSize) != 0)
            return null;

        var elementSize = MetadataElementSize(elementType, pointerSize);
        if (elementSize <= 0)
            return null;

        return StructElementIndex(memory, array, elementSize, pointerSize, definitions) is { } index
            ? new AddressOf(new ArrayAccess(array, index))
            : null;
    }

    private static bool IsMemoryBase(IOperand operand, LocalVariable local)
        => operand is MemoryOperand { Base: LocalVariable baseLocal } && ReferenceEquals(baseLocal, local);

    private static long MetadataElementSize(TypeAnalysisContext elementType, int pointerSize)
        => TypeSizes.UnboxedSize(elementType, pointerSize);

    private static IOperand? StructElementIndex(MemoryOperand memory, LocalVariable array, long elementSize, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var indexAffine = memory.Index is LocalVariable indexLocal
            ? ScaleBy(Evaluate(indexLocal, definitions, 0), Math.Max(memory.Scale, 1))
            : new Affine(null, 0, 0);

        if (Sum(indexAffine, new Affine(null, 0, memory.Addend)) is not { } address)
            return null;

        if (ReferenceEquals(address.Root, array))
            return null;

        var offset = address.Offset - ElementsOffset(pointerSize);

        if (address.Root != null)
            return address.Multiplier == elementSize && offset == 0 ? address.Root : null;

        return offset >= 0 && offset % elementSize == 0 ? new Immediate(offset / elementSize) : null;
    }

    // value = Multiplier * Root + Offset (a null Root means it's just a constant)
    private readonly record struct Affine(LocalVariable? Root, long Multiplier, long Offset);

    private static Affine? Evaluate(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        if (depth > 8)
            return null;

        switch (operand)
        {
            case Immediate { Value: var value }:
                return new Affine(null, 0, value);

            case LocalVariable local:
            {
                if (!definitions.TryGetValue(local, out var definition) || definition == null)
                    return new Affine(local, 1, 0);

                return definition switch
                {
                    { OpCode: OpCode.Move, Operands: [_, MemoryOperand lea] } => EvaluateLea(lea, definitions, depth + 1),
                    { OpCode: OpCode.Move, Operands: [_, var source] } => Evaluate(source, definitions, depth + 1),
                    { OpCode: OpCode.Add, Operands: [_, var left, var right] } => Sum(Evaluate(left, definitions, depth + 1), Evaluate(right, definitions, depth + 1)),
                    { OpCode: OpCode.ShiftLeft, Operands: [_, var left, Immediate { Value: >= 0 and < 32 } shift] } => ScaleBy(Evaluate(left, definitions, depth + 1), 1L << (int)shift.Value),
                    { OpCode: OpCode.Multiply, Operands: [_, var left, Immediate factor] } => ScaleBy(Evaluate(left, definitions, depth + 1), factor.Value),
                    _ => new Affine(local, 1, 0)
                };
            }

            default:
                return null;
        }
    }

    private static Affine? EvaluateLea(MemoryOperand lea, Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        var result = (Affine?)new Affine(null, 0, lea.Addend);

        if (lea.Base != null)
            result = Sum(result, Evaluate(lea.Base, definitions, depth));

        if (lea.Index != null)
            result = Sum(result, ScaleBy(Evaluate(lea.Index, definitions, depth), Math.Max(lea.Scale, 1)));

        return result;
    }

    private static Affine? Sum(Affine? left, Affine? right)
    {
        if (left is not { } l || right is not { } r)
            return null;

        if (l.Root != null && r.Root != null && !ReferenceEquals(l.Root, r.Root))
            return null;

        return new Affine(l.Root ?? r.Root, l.Multiplier + r.Multiplier, l.Offset + r.Offset);
    }

    private static Affine? ScaleBy(Affine? value, long factor)
        => value is { } affine ? new Affine(affine.Root, affine.Multiplier * factor, affine.Offset * factor) : null;

    // null means the local has more than one definition
    private static Dictionary<LocalVariable, Instruction?> SingleDefinitions(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, Instruction?>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = definitions.ContainsKey(destination) ? null : instruction;

        return definitions;
    }

    private static Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> CollectUses(ISILControlFlowGraph cfg)
    {
        var uses = new Dictionary<LocalVariable, List<(Instruction, int)>>();

        foreach (var instruction in cfg.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (ReferenceEquals(operand, instruction.Destination))
                    continue;

                foreach (var local in OperandLocals(operand))
                {
                    if (!uses.TryGetValue(local, out var sites))
                        uses[local] = sites = [];
                    sites.Add((instruction, i));
                }
            }
        }

        return uses;
    }

    private static IEnumerable<LocalVariable> OperandLocals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable direct:
                yield return direct;
                break;
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal)
                    yield return baseLocal;
                if (memory.Index is LocalVariable indexLocal)
                    yield return indexLocal;
                break;
            case AddressOf { Target: LocalVariable addressed }:
                yield return addressed;
                break;
        }
    }
}
