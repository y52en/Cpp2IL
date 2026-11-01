using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

public static class MetadataResolver
{
    public static void ResolveAll(MethodAnalysisContext method)
    {
        ResolveStringLiteralAccessors(method);
        ResolveCalls(method);
        ResolveGetter(method);
        ResolveMetadataUsages(method);
    }

    private static void ResolveStringLiteralAccessors(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[1] is not LocalVariable result)
                continue;

            for (var i = 2; i < instruction.Operands.Count; i++)
            {
                if (LiteralSlotAddress(instruction.Operands[i], definitions) is not { } address
                    || libContext.GetLiteralByAddress(address) is not { } literal)
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new StringLiteral(literal));
                break;
            }
        }
    }

    private static ulong? LiteralSlotAddress(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        operand switch
        {
            Immediate immediate => immediate.UnsignedValue,
            LocalVariable local when definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, Immediate immediate] } => immediate.UnsignedValue,
            _ => null,
        };

    /// <summary>
    /// Resolves <c>Move local, [absoluteAddress]</c> loads of IL2CPP metadata-usage globals into a
    /// strongly-typed operand: a string literal, a <see cref="TypeAnalysisContext"/> (an Il2CppType*/
    /// Il2CppClass* usage) or, for a MethodInfo* usage, a <see cref="RuntimeMethodInfoAnalysisContext"/>
    /// naming the method it refers to (also used to type the local - see <see cref="LocalVariables"/>),
    /// or likewise a <see cref="RuntimeFieldInfoAnalysisContext"/> for a FieldInfo* usage.
    /// </summary>
    internal static void ResolveMetadataUsages(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;
        var allDefinitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(group => group.Key, group => group.ToArray());
        var definitions=allDefinitions.Where(group=>group.Value.Length==1)
            .ToDictionary(group=>group.Key,group=>group.Value[0]);
        DominatorInfo? gotDominance=null;

        ulong? ReadGot(ulong slot) => method.AppContext.Binary is ElfFile elf && elf.IsGlobalOffsetTableEntry(slot)
            ? elf.ReadPointerAtVirtualAddress(slot) : null;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move)
                continue;

            if (instruction.Operands[0] is not LocalVariable)
                continue;

            var address = instruction.Operands[1] switch
            {
                MemoryOperand { Base: null, Index: null, Scale: 0 } memory => (ulong)memory.Addend,
                Immediate immediate => immediate.UnsignedValue,
                _ => IndirectMetadataAddress(instruction.Operands[1], definitions, ReadGot)
                    ?? PhiGotMetadataAddress(instruction,method.ControlFlowGraph,definitions,
                        method.AppContext.Binary.PointerSizeBytes,ReadGot)
                    ?? RepeatedGotMetadataAddress(instruction,method.ControlFlowGraph,allDefinitions,
                        method.AppContext.Binary.PointerSizeBytes,ReadGot,ref gotDominance) ?? 0ul,
            };

            if (address == 0)
                continue;

            // String literal.
            var stringLiteral = libContext.GetLiteralByAddress(address);
            if (stringLiteral != null)
            {
                instruction.SetOperand(1, new StringLiteral(stringLiteral));
                continue;
            }

            // Type metadata usage (Il2CppType* / Il2CppClass*).
            if (method.DeclaringType is { } declaringType)
            {
                var typeGlobal = libContext.GetTypeGlobalByAddress(address);
                if (typeGlobal != null)
                {
                    instruction.SetOperand(1, declaringType.AppContext.ResolveIl2CppType(typeGlobal));
                    continue;
                }
            }

            // Method metadata usage (MethodInfo*). On metadata v27+ GetMethodGlobalByAddress can return
            // any global, so confirm it is actually a method before resolving - the resolver's switch
            // throws on other usage kinds.
            var methodUsage = libContext.GetMethodGlobalByAddress(address);
            if (methodUsage?.Type is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef
                && method.AppContext.ResolveContextForMethod(methodUsage) is { DeclaringType: { } methodDeclaringType } methodContext)
            {
                instruction.SetOperand(1, new RuntimeMethodInfoAnalysisContext(methodContext, methodDeclaringType.DeclaringAssembly));
                continue;
            }

            // Field metadata usage (FieldInfo*), e.g. the RuntimeFieldHandle passed to InitializeArray.
            if (libContext.GetRawFieldGlobalByAddress(address) is { Type: MetadataUsageType.FieldInfo } fieldUsage
                && method.AppContext.ResolveContextForField(fieldUsage.AsField()) is { DeclaringType.DeclaringAssembly: { } fieldAssembly } fieldContext)
                instruction.SetOperand(1, new RuntimeFieldInfoAnalysisContext(fieldContext, fieldAssembly));
        }
    }

    // LDR pointer, [GOT slot]; LDR value, [pointer] loads a metadata usage,
    // not the usage's address. Resolve only the second load; normal DCE can
    // remove the first once dead. All returned addresses still need an exact
    // authoritative metadata-usage match in ResolveMetadataUsages.
    internal static ulong? IndirectMetadataAddress(IOperand operand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, Func<ulong, ulong?> readGot)
    {
        if (operand is not MemoryOperand { Base: LocalVariable pointer, Index: null, Scale: 0, Addend: 0 }
            || !definitions.TryGetValue(pointer, out var definition)
            || definition is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: null, Index: null, Scale: 0 } slot] })
            return null;
        return readGot(unchecked((ulong)slot.Addend));
    }

    // A saved GOT pointer may meet itself (or an identical reload) at SSA
    // phis. Resolve a VALUE only when every incoming dependency is an exact
    // pointer-sized GOT load/copy and every cycle reaches a real GOT anchor.
    // A valid sibling must never legitimize a separate uninitialized cycle.
    // The returned address STILL needs the original metadata-usage lookup.
    internal static ulong? PhiGotMetadataAddress(Instruction consumer,ISILControlFlowGraph graph,
        IReadOnlyDictionary<LocalVariable,Instruction> definitions,int pointerSize,Func<ulong,ulong?> readGot)
    {
        if(pointerSize is not (4 or 8) || consumer.NativeReadSize!=pointerSize
            || consumer is not {OpCode:OpCode.Move,Operands:[_,MemoryOperand {Base:LocalVariable pointer,Index:null,Scale:0,Addend:0}]}
            || !definitions.TryGetValue(pointer,out var origin)
            || !(origin.OpCode==OpCode.Phi || origin is {OpCode:OpCode.Move,Operands:[_,LocalVariable]}))return null;
        var edges=new Dictionary<LocalVariable,LocalVariable[]>();var anchors=new HashSet<LocalVariable>();
        var addresses=new HashSet<ulong>();var pending=new Stack<LocalVariable>();pending.Push(pointer);
        while(pending.Count>0)
        {
            var local=pending.Pop();if(edges.ContainsKey(local))continue;
            if(edges.Count>=256 || !definitions.TryGetValue(local,out var definition))return null;
            LocalVariable[] dependencies;
            if(definition is {OpCode:OpCode.Move,Operands:[_,MemoryOperand {Base:null,Index:null,Scale:0} slot]}
                && definition.NativeReadSize==pointerSize
                && readGot(unchecked((ulong)slot.Addend)) is {} address)
            {anchors.Add(local);addresses.Add(address);dependencies=[];}
            else if(definition is {OpCode:OpCode.Move,Operands:[_,LocalVariable source]}
                && (definition.NativeRegisterCopySize==0 || definition.NativeRegisterCopySize==pointerSize))dependencies=[source];
            else if(definition.OpCode==OpCode.Phi && definition.Operands.Count>=2
                && definition.Operands.Skip(1).All(o=>o is LocalVariable))dependencies=definition.Operands.Skip(1).Cast<LocalVariable>().ToArray();
            else return null;
            edges[local]=dependencies;foreach(var dependency in dependencies)pending.Push(dependency);
        }
        if(anchors.Count==0 || addresses.Count!=1)return null;
        if(graph.Instructions.Any(i=>i.ImplicitDefinition is {} clobbered
            && edges.Keys.Any(local=>local.Register.Number==clobbered.Number
                && local.Register.Name==clobbered.Name)))return null;
        var anchored=new HashSet<LocalVariable>(anchors);var changed=true;
        while(changed)
        {
            changed=false;
            foreach(var (local,dependencies) in edges)
                if(!anchored.Contains(local) && dependencies.Any(anchored.Contains))changed|=anchored.Add(local);
        }
        if(anchored.Count!=edges.Count)return null;
        var origins=graph.Blocks.Where(b=>b.Instructions.Contains(origin)).ToArray();
        var consumers=graph.Blocks.Where(b=>b.Instructions.Contains(consumer)).ToArray();
        if(origins.Length!=1 || consumers.Length!=1)return null;
        if(ReferenceEquals(origins[0],consumers[0]))
        {if(origins[0].Instructions.IndexOf(origin)>=origins[0].Instructions.IndexOf(consumer))return null;}
        else if(!new DominatorInfo(graph).Dominates(origins[0],consumers[0]))return null;
        return addresses.Single();
    }

    // Post-SSA local coalescing can reuse a pointer for identical GOT loads.
    // All writes must load the SAME exact pointer-sized GOT slot, and at least
    // one write must actually dominate this use. Equal values alone do not
    // prove initialization on an alternate entry/branch. The returned address
    // still needs the authoritative metadata-usage lookup above.
    internal static ulong? RepeatedGotMetadataAddress(Instruction consumer,ISILControlFlowGraph graph,
        IReadOnlyDictionary<LocalVariable,Instruction[]> definitions,int pointerSize,
        Func<ulong,ulong?> readGot,ref DominatorInfo? dominance)
    {
        if(pointerSize is not (4 or 8) || consumer.OpCode!=OpCode.Move || consumer.NativeReadSize!=pointerSize
            || consumer.Operands is not [_,MemoryOperand {Base:LocalVariable pointer,Index:null,Scale:0,Addend:0}]
            || !definitions.TryGetValue(pointer,out var writes) || writes.Length<2)return null;
        if(writes.Any(i=>i.OpCode!=OpCode.Move || i.NativeReadSize!=pointerSize
            || i.Operands is not [_,MemoryOperand {Base:null,Index:null,Scale:0}]))return null;
        var slots=writes.Select(i=>unchecked((ulong)((MemoryOperand)i.Operands[1]).Addend)).Distinct().ToArray();
        if(slots.Length!=1 || readGot(slots[0]) is not { } address)return null;
        if(graph.Instructions.Any(i=>i.ImplicitDefinition is { } register
            && register.Number==pointer.Register.Number && register.Name==pointer.Register.Name))return null;
        var consumers=graph.Blocks.Where(b=>b.Instructions.Contains(consumer)).ToArray();
        if(consumers.Length!=1 || graph.Blocks.Any(b=>b.Predecessors.Any(p=>!graph.Blocks.Contains(p))))return null;
        var target=consumers[0];
        foreach(var write in writes)
        {
            var blocks=graph.Blocks.Where(b=>b.Instructions.Contains(write)).ToArray();
            if(blocks.Length!=1)return null;
            if(ReferenceEquals(blocks[0],target))
            {
                if(target.Instructions.IndexOf(write)<target.Instructions.IndexOf(consumer))return address;
            }
            else
            {
                dominance??=new DominatorInfo(graph);
                if(dominance.Dominates(blocks[0],target))return address;
            }
        }
        return null;
    }

    /// <summary>
    /// Replaces every <c>[base + addend]</c> memory operand whose base is a typed local with a
    /// <see cref="FieldReference"/> to the field at that offset. Returns whether any operand was
    /// resolved this pass, so the type/field fixpoint can detect convergence: as more bases become
    /// typed (a field load types its result, which is the base of the next load), more offsets
    /// resolve, so this is re-run until it stops finding new fields.
    /// </summary>
    public static bool ResolveFieldOffsets(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is not MemoryOperand memory)
                    continue;

                // Has to be [base (local) + addend (field offset)]
                if (memory.Index != null || memory.Scale != 0)
                    continue;

                if (memory.Base is not LocalVariable local || local?.Type == null)
                    continue;

                // check if static field access
                var staticOwner = (local.Type as StaticFieldStorageTypeAnalysisContext)?.OwnerType;
                var owner = staticOwner ?? (local.Type is ByRefTypeAnalysisContext byref ? byref.ElementType : local.Type);
                // A checked-unbox scalar root dereferences the boxed value,
                // not its private runtime backing field. Ordinary ref/out
                // parameters retain their existing field/type inference path.
                if (local.Type is CheckedUnboxRecovery.UnboxedReference && TypeSizes.IsScalarValueType(owner)) continue;
                var nativeWidth=i==0 ? instruction.NativeWriteSize : i==1 ? instruction.NativeReadSize : 0;
                if(instruction.OpCode==OpCode.Move && nativeWidth>0 && staticOwner==null
                    && NestedFieldAccess.Find(owner,local,memory.Addend,nativeWidth,method) is { } nested)
                {
                    instruction.SetOperand(i,nested);changed=true;continue;
                }
                var genericOwner = owner as GenericInstanceTypeAnalysisContext;

                // Exact-width nested lookup above owns closed generic values.
                // Do not fall back to the legacy reference-object header/zero
                // metadata offsets for padding, split stores or partial reads.
                if(staticOwner==null && owner.IsValueType && genericOwner!=null
                    && (!owner.HasAnyGenericParameters() || SharedGenericReturnLayout.FieldsFor(method,owner)!=null))continue;

                if (staticOwner == null && GenericInstanceFieldLayout.FindInheritedFieldAtOffset(owner, memory.Addend, nativeWidth) is { } inherited)
                {
                    instruction.SetOperand(i, new FieldReference(inherited, local, (int)memory.Addend));
                    changed = true;
                    continue;
                }

                FieldAnalysisContext? field;
                if (genericOwner != null && staticOwner == null)
                {
                    // metadata has all-0 offsets for generic definitions, so recompute layout
                    // TODO support user-defined value types
                    if (genericOwner.GenericArguments.Any(a => a.IsValueType))
                        continue;

                    field = GenericInstanceFieldLayout.FindFieldAtOffset(genericOwner.GenericType, memory.Addend);
                }
                else if (staticOwner == null && owner.GenericParameters.Count > 0)
                {
                    field = GenericInstanceFieldLayout.FindFieldAtOffset(owner, memory.Addend);
                }
                else
                {
                    // an inherited field exists on the base type but sits at the same offset in the
                    // derived layout, so the whole chain is searched
                    field = null;
                    for (var candidateOwner = genericOwner?.GenericType ?? owner; candidateOwner != null && field == null; candidateOwner = candidateOwner.BaseType)
                        field = candidateOwner.Fields.FirstOrDefault(f => f.IsStatic == (staticOwner != null)
                            && (f.Attributes & FieldAttributes.Literal) == 0 // consts have no storage but their metadata offset is 0, which would match
                            && f.BackingData?.FieldOffset == memory.Addend);
                }

                if (field == null) // TODO: Support nested fields (Field1.Field2.Field3)
                    continue;

                // make sure we have a full GIT for field access. open type is bad.
                if (genericOwner != null)
                    field = new ConcreteGenericFieldAnalysisContext(field, genericOwner);

                instruction.SetOperand(i, new FieldReference(field, local, (int)memory.Addend));
                changed = true;
            }
        }

        return changed;
    }

    internal static void RewriteNamedExceptionCall(MethodAnalysisContext method, Instruction call,
        TypeAnalysisContext thrown, bool unconditionalRaiser)
    {
        // Raw argument padding may appear to read a nonexistent return value.
        // Positively proven nonreturning transport always terminates the path.
        if (!unconditionalRaiser && call.Destination is LocalVariable produced
            && method.ControlFlowGraph!.Instructions.Any(i => i.Sources.Any(s => ReferenceEquals(s, produced))))
        {
            call.OpCode = OpCode.Newobj;
            call.SetOperands(produced, thrown);
        }
        else
        {
            call.OpCode = OpCode.Throw;
            call.SetOperands(thrown);
        }
    }

    private static void ResolveCalls(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            if (block.BlockType != BlockType.Call && block.BlockType != BlockType.TailCall)
                continue;

            var callInstruction = block.Instructions[^1];
            if (callInstruction.Operands[0] is not Immediate dest)
                continue;

            var target = dest.UnsignedValue;
            if (callInstruction.NativeDirectCallTarget == 0)
                callInstruction.NativeDirectCallTarget = target;

            var keyFunctionAddresses = method.AppContext.GetOrCreateKeyFunctionAddresses();

            if (keyFunctionAddresses.IsKeyFunctionAddress(target))
            {
                HandleKeyFunction(method.AppContext, callInstruction, target, keyFunctionAddresses);

                if (target == keyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline
                    && callInstruction is { OpCode: OpCode.Call, Operands: [_, var initResult, var handle, ..] })
                {
                    callInstruction.OpCode = OpCode.Move;
                    callInstruction.SetOperands(initResult, handle);
                }

                continue;
            }

            //Non-key function call. Try to find a single match
            if (!method.AppContext.MethodsByAddress.TryGetValue(target, out var targetMethods))
            {
                // Not a managed method at all. It may be one of the runtime helpers built around an exception
                // type, which either throw it themselves or build it and hand it back for the caller to raise.
                if (ThrowHelperRecovery.GetThrownException(method.AppContext, target) is { } thrown)
                {
                    RewriteNamedExceptionCall(method, callInstruction, thrown,
                        ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target));

                    continue;
                }

                // Otherwise it may be one of the raisers, which throw the exception they are given
                var raisedIndex = callInstruction.OpCode == OpCode.CallVoid ? 1 : 2;

                if (callInstruction.Operands.Count > raisedIndex && ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target))
                {
                    var raised = callInstruction.Operands[raisedIndex];

                    callInstruction.OpCode = OpCode.Throw;
                    callInstruction.SetOperands(raised);
                }

                continue;
            }

            // Duplicated/Shared method bodies are resolved later in ResolveCallsViaMethodInfo/ResolveAmbiguousCalls.
            if (targetMethods is not [{ } singleTargetMethod])
                continue;

            callInstruction.SetOperand(0, singleTargetMethod);
            singleTargetMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(callInstruction, singleTargetMethod);
        }

        method.ControlFlowGraph.MergeCallBlocks();
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by matching the receiver's known
    /// type against the candidates' declaring types. Runs inside the type/field fixpoint and so
    /// re-fires as receivers become typed - a resolved call types its return value, which can type
    /// the receiver of a further call. Returns whether any call was resolved this pass.
    ///
    /// Conservative by design: it commits only when exactly one non-static candidate's declaring
    /// type matches the receiver's type. Anything still untyped or ambiguous is left for a later
    /// pass, or left unresolved - it never guesses.
    /// </summary>
    public static bool ResolveAmbiguousCalls(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            // A resolved call's target is a method/key-function name; only unresolved ones are still numeric.
            if (instruction.Operands[0] is not Immediate target)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates) || candidates.Count < 2)
                continue;

            // e.g. string.Equals and string.op_Equality, identical params, instance type, and bodies are shared
            // we can't differentiate which is being called but it doesn't matter
            if (AreInterchangeable(candidates))
            {
                var preferred = PreferredOf(candidates);
                instruction.SetOperand(0, preferred);
                preferred.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, preferred);
                changed = true;
                continue;
            }

            if (GetReceiver(instruction) is not { Type: { } receiverType } receiver)
                continue;

            // Prefer picking base ctor if we are a ctor
            var callerIsCtor = method.Name == ".ctor" && receiver.IsThis;

            // Handle methods with shared bodies
            var match = default(MethodAnalysisContext);

            for (var type = receiverType; type != null && match == null; type = type.BaseType)
            {
                var matches = candidates.Where(c => !c.IsStatic && IsSameType(c.DeclaringType, type)).ToList();

                if (matches.Count > 1 && callerIsCtor)
                    matches = matches.Where(c => c.Name == ".ctor").ToList();

                if (matches.Count > 1)
                    break;

                match = matches.SingleOrDefault();
            }

            if (match == null)
                continue;

            instruction.SetOperand(0, match);
            match.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, match);
            changed = true;
        }

        return changed;
    }

    private static bool AreInterchangeable(List<MethodAnalysisContext> candidates)
    {
        var first = candidates[0];

        return candidates.All(c => c.IsStatic == first.IsStatic
            && ReferenceEquals(c.DeclaringType, first.DeclaringType)
            && ReferenceEquals(c.ReturnType, first.ReturnType)
            && c.Parameters.Count == first.Parameters.Count
            && SameParameterTypes(c, first));
    }

    private static bool SameParameterTypes(MethodAnalysisContext a, MethodAnalysisContext b)
    {
        for (var i = 0; i < a.Parameters.Count; i++)
        {
            if (!ReferenceEquals(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType))
                return false;
        }

        return true;
    }

    // Prefer operators if possible
    private static MethodAnalysisContext PreferredOf(List<MethodAnalysisContext> candidates) =>
        candidates.FirstOrDefault(c => c.Name.StartsWith("op_")) ?? candidates[0];

    // The receiver ('this') of a call is the first integer-slot argument: operand 1 for CallVoid
    // (after the target), operand 2 for Call (after the target and the return value).
    // A value type receiver is passed byref, so it arrives as an AddressOf over the local.
    private static LocalVariable? GetReceiver(Instruction call)
    {
        var index = call.OpCode == OpCode.CallVoid ? 1 : 2;

        return index < call.Operands.Count
            ? call.Operands[index] switch
            {
                LocalVariable local => local,
                AddressOf { Target: LocalVariable addressed } => addressed,
                _ => null
            }
            : null;
    }

    // Concrete generic method contexts build their declaring type fresh rather than via the
    // GetOrCreate cache, so generic instances also need comparing structurally.
    // TODO Fix this, concrete generic methods should use GetOrCreate
    private static bool IsSameType(TypeAnalysisContext? a, TypeAnalysisContext? b)
    {
        if (ReferenceEquals(a, b))
            return true;

        if (a is not GenericInstanceTypeAnalysisContext leftInstance
            || b is not GenericInstanceTypeAnalysisContext rightInstance
            || !ReferenceEquals(leftInstance.GenericType, rightInstance.GenericType)
            || leftInstance.GenericArguments.Count != rightInstance.GenericArguments.Count)
            return false;

        for (var i = 0; i < leftInstance.GenericArguments.Count; i++)
        {
            if (!IsSameType(leftInstance.GenericArguments[i], rightInstance.GenericArguments[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Resolves any Call (theoretically should always be a CallVoid) target directly after a Newobj to a constructor call.
    /// </summary>
    public static bool ResolveConstructorCalls(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable definition)
                definitions[definition] = instruction;

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate callTarget)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(callTarget.UnsignedValue, out var candidates))
                continue;

            if (GetReceiver(instruction) is not { } receiver || AllocatedType(receiver, definitions) is not { } allocatedType)
                continue;

            var constructor = candidates.FirstOrDefault(c => !c.IsStatic && c.Name == ".ctor" && ReferenceEquals(c.DeclaringType, allocatedType))
                              ?? FindConstructorForSharedBody(allocatedType, candidates);
            if (constructor == null)
                continue;

            instruction.SetOperand(0, constructor);
            constructor.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, constructor);
            changed = true;
        }

        return changed;
    }

    private static MethodAnalysisContext? FindConstructorForSharedBody(TypeAnalysisContext allocatedType, List<MethodAnalysisContext> candidates)
    {
        var candidateParamCounts = new HashSet<int>(candidates
            .Where(c => c is { IsStatic: false, Name: ".ctor" })
            .Select(c => c.Parameters.Count));

        if (candidateParamCounts.Count == 0)
            return null;

        var definition = allocatedType is GenericInstanceTypeAnalysisContext genericInstance ? genericInstance.GenericType : allocatedType;
        var matches = definition.Methods
            .Where(m => m is { IsStatic: false, Name: ".ctor" } && candidateParamCounts.Contains(m.Parameters.Count))
            .ToList();

        if (matches is not [{ } match])
            return null;

        return allocatedType is GenericInstanceTypeAnalysisContext instance
            ? new ConcreteGenericMethodAnalysisContext(match, instance.GenericArguments, [])
            : match;
    }

    // Follow SSA copies from a local back to the Newobj that produced the value
    private static TypeAnalysisContext? AllocatedType(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local) && definitions.TryGetValue(local, out var definition))
        {
            switch (definition.OpCode)
            {
                case OpCode.Newobj:
                    return definition.Operands.Count == 2
                        ? TrivialConstructorRecovery.AllocationType(definition.Operands[1]) : null;
                case OpCode.Move when definition.Operands[1] is LocalVariable source:
                    local = source;
                    continue;
            }

            break;
        }

        return null;
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by reading the runtime
    /// <c>MethodInfo*</c> the caller passes in, if there is one.
    /// </summary>
    public static bool ResolveCallsViaMethodInfo(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (instruction.Operands[0] is MethodAnalysisContext)
            {
                changed |= RefineResolvedGenericCall(method, instruction);
                continue;
            }

            if (instruction.Operands[0] is not Immediate target)
                //Already resolved
                continue;

            if (NativeReceiverCounterpartRecovery.TryResolve(method,instruction))
            {
                changed = true;
                continue;
            }

            if (NativeNullableAccessorRecovery.TryResolve(method, instruction))
            {
                changed = true;
                continue;
            }

            if (!method.AppContext.MethodsByAddress.ContainsKey(target.UnsignedValue)
                && NativeNullableConstructorRecovery.IsProvenBody(method, target.UnsignedValue))
            {
                changed |= NativeNullableConstructorRecovery.TryResolve(method, instruction);
                continue;
            }

            if (GetMethodInfoArgument(instruction) is not { RepresentedMethod: { } representedMethod })
                //No MethodInfo to work with
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates))
            {
                // A MethodInfo surviving in an unused argument register is
                // not a native callee identity. Require this metadata method's
                // own actual native entry (or its architecture-proven unboxed
                // entry); never turn an unknown runtime helper into a ctor.
                if (!UnmappedNativeEntryMatches(representedMethod,target.UnsignedValue))
                    continue;
                // However, make sure it isn't our OWN hidden MethodInfo arg, because that would turn all unknown calls into recursion
                if (ReferenceEquals(representedMethod, method))
                    continue;

                var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                var hiddenParamIndex = firstArg
                    + (representedMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(representedMethod) == true ? 1 : 0)
                    + (representedMethod.IsStatic ? 0 : 1) + representedMethod.Parameters.Count;

                if (hiddenParamIndex >= instruction.Operands.Count
                    || AsMethodInfo(instruction.Operands[hiddenParamIndex]) is not { } passedInfo
                    || !ReferenceEquals(passedInfo.RepresentedMethod,representedMethod))
                    continue;

                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                changed = true;
                continue;
            }

            if (candidates.Count < 2)
                continue;

            //Try to actually match on the method name so we don't just replace a call with something else.
            var representedBase = BaseMethodOf(representedMethod);
            if (!candidates.Any(candidate => ReferenceEquals(BaseMethodOf(candidate), representedBase)))
                continue;

            instruction.SetOperand(0, representedMethod);
            representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
            changed = true;
        }

        return changed;
    }

    internal static bool UnmappedNativeEntryMatches(MethodAnalysisContext method,ulong entry)
    {
        if(entry==0)return false;
        try
        {
            var architecture=method.AppContext.InstructionSet;
            var unboxed=architecture.GetUnboxedMethodTarget(method);
            var actual=unboxed!=0?unboxed:architecture.GetPointerForMethod(method);
            if(actual!=0)return actual==entry || NativeRegisteredReceiverLeafProofs.Matches(method,entry);
            // RGCTX inflation can create a metadata-identical synthetic closed
            // context without carrying its registered native MethodSpec. It is
            // still not evidence by itself: require an independently registered
            // concrete context for the exact definition and all type arguments,
            // with its own architecture-proven entry equal to this call target.
            if(method is not ConcreteGenericMethodAnalysisContext concrete)return false;
            foreach(var registered in RegisteredMethodIdentityIndex.Candidates(method))
            {
                if(registered.MethodRef==null
                    || !ReferenceEquals(registered.BaseMethodContext,concrete.BaseMethodContext)
                    || registered.IsStatic!=concrete.IsStatic
                    || registered.TypeGenericParameters.Count!=concrete.TypeGenericParameters.Count
                    || registered.MethodGenericParameters.Count!=concrete.MethodGenericParameters.Count
                    || !registered.TypeGenericParameters.Zip(concrete.TypeGenericParameters,TrivialConstructorRecovery.SameType).All(equal=>equal)
                    || !registered.MethodGenericParameters.Zip(concrete.MethodGenericParameters,TrivialConstructorRecovery.SameType).All(equal=>equal)
                    || !TrivialConstructorRecovery.SameType(registered.ReturnType,concrete.ReturnType)
                    || registered.Parameters.Count!=concrete.Parameters.Count
                    || !registered.Parameters.Zip(concrete.Parameters,(a,b)=>TrivialConstructorRecovery.SameType(a.ParameterType,b.ParameterType)).All(equal=>equal))
                    continue;
                var registeredUnboxed=architecture.GetUnboxedMethodTarget(registered);
                var registeredEntry=registeredUnboxed!=0?registeredUnboxed:architecture.GetPointerForMethod(registered);
                if(registeredEntry!=0 && (registeredEntry==entry || NativeRegisteredReceiverLeafProofs.Matches(registered,entry)))return true;
            }
            return false;
        }
        catch(Exception){return false;}
    }

    internal static bool RefineResolvedGenericCall(MethodAnalysisContext caller, Instruction call,
        Func<MethodAnalysisContext, ulong, bool>? nativeEntryMatches = null)
    {
        if (!call.IsCall || call.NativeVirtualDispatch || call.NativeDirectCallTarget == 0
            || call.Operands.Count == 0 || call.Operands[0] is not MethodAnalysisContext current
            || current is ConcreteGenericMethodAnalysisContext || current.DeclaringType is not { GenericParameters.Count: > 0 }
            || current.DeclaringType is GenericInstanceTypeAnalysisContext || current.GenericParameters.Count != 0
            || current.Parameters.Count != 0) return false;
        var hidden = (call.OpCode == OpCode.Call ? 2 : 1) + (current.IsStatic ? 0 : 1);
        if (call.Operands.Count != hidden + 1
            || AsMethodInfo(call.Operands[hidden]) is not { RepresentedMethod: ConcreteGenericMethodAnalysisContext concrete }
            || ReferenceEquals(concrete, caller) || !ReferenceEquals(BaseMethodOf(current), BaseMethodOf(concrete))
            || concrete.MethodGenericParameters.Count != 0 || concrete.IsStatic != current.IsStatic
            || concrete.DeclaringType is not GenericInstanceTypeAnalysisContext closed
            || closed.HasAnyGenericParameters()
            || !TrivialConstructorRecovery.SameType(current.ReturnType, concrete.ReturnType)
            || current.ReturnType.HasAnyGenericParameters()
            || current.ReturnType is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
                or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext) return false;
        nativeEntryMatches ??= (target, entry) =>
        {
            var architecture = target.AppContext.InstructionSet;
            var unboxed = architecture.GetUnboxedMethodTarget(target);
            var actual = unboxed != 0 ? unboxed : architecture.GetPointerForMethod(target);
            if (actual != 0) return actual == entry;
            // A metadata-only closed instance may still have its own exact
            // registered native variant. Use the same definition/arguments/
            // signature/native-entry proof as unresolved MethodInfo calls;
            // value arguments do not authorize reference-sharing fallback.
            if (UnmappedNativeEntryMatches(target, entry)) return true;
            // A stripped MethodSpec can have no separate native variant while
            // still supplying the exact closed metadata for a reference-shared
            // body. Require the SAME definition's proven native entry too;
            // never apply this route to value/open/pointer arguments.
            if (concrete.MethodRef == null || !ClosedReferenceOwnerArguments(closed)) return false;
            var definitionUnboxed = architecture.GetUnboxedMethodTarget(current);
            var definitionEntry = definitionUnboxed != 0 ? definitionUnboxed : architecture.GetPointerForMethod(current);
            return definitionEntry != 0 && definitionEntry == entry;
        };
        if (!nativeEntryMatches(concrete, call.NativeDirectCallTarget)) return false;
        // Already remapped operands: same fixed return, zero explicit args and
        // same instance/static ABI. Do not remap or infer new argument slots.
        call.SetOperand(0, concrete);
        return true;
    }

    internal static bool ClosedReferenceOwnerArguments(GenericInstanceTypeAnalysisContext owner)
        => owner.GenericArguments.Count > 0 && owner.GenericArguments.Count == owner.GenericType.GenericParameters.Count
            && owner.GenericArguments.All(argument => !argument.IsValueType && !argument.HasAnyGenericParameters()
                && argument is not (PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
                    or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext));

    // Resolves virtual dispatch through <c>[klass + vtableOffset + slot * sizeof(VirtualInvokeData)]</c>
    // as long as the klass local's represented type is known.
    public static bool ResolveVirtualCalls(MethodAnalysisContext method)
        => ResolveVirtualCalls(method, RuntimeMetadataLayout.For(method));

    internal static bool ResolveVirtualCalls(MethodAnalysisContext method, RuntimeMetadataLayout layout,
        IReadOnlySet<Instruction>? allowedCalls = null)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = layout.VTable;
        var invokeDataSize = 2L * pointerSize;
        var changed = false;

        var loads = new Dictionary<LocalVariable, MemoryOperand>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is MemoryOperand { Index: null, Scale: 0 } load)
                loads[destination] = load;
        }

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (allowedCalls != null && !allowedCalls.Contains(instruction)) continue;
            if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                continue;

            if (SlotLoad(instruction.Operands[0]) is not { } target
                || target.Base is not LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } receiverType } } klassLocal)
                continue;

            var offset = target.Addend - vtableOffset;
            if (offset < 0 || offset % invokeDataSize != 0)
                continue;

            var slot = (int)(offset / invokeDataSize);
            var implementation = receiverType is SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext
                ? pointerSize == 8 && layout.VTable == 0x128
                    ? ResolveArrayObjectSlot(method.AppContext, receiverType, slot) : null
                : ResolveVTableSlot(method.AppContext, receiverType, slot);
            if (implementation is not { } resolved)
                continue;
            if (resolved.IsStatic)
                continue;

            var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
            var tail = instruction.OpCode == OpCode.IndirectJump;
            var resolver = resolved.AppContext.InstructionSet.CallingConventionResolver;
            LocalVariable? tailResult = null;
            if (tail)
            {
                // A tail branch's operand 1 is a stale native return register use,
                // not a managed result definition. Never reuse it as the result.
                if (!method.IsVoid && (resolved.IsVoid || !TrivialConstructorRecovery.SameType(method.ReturnType, resolved.ReturnType))
                    || resolver == null
                    || resolver.ResolveForManaged(resolved).Any(o=>o is StackOffset)
                    || resolved.Parameters.Any(p=>Arm64HfaLayout.Fields(p.ParameterType)!=null))
                    continue; // These ABI shapes require separate proven recovery.
                var operands = new List<IOperand>{resolved};
                if (!resolved.IsVoid)
                {
                    tailResult = new LocalVariable("virtualTailCallResult_"+instruction.Index,
                        new Register(null,"virtual_tail_result_"+instruction.Index), resolved.ReturnType);
                    method.Locals.Add(tailResult);
                    operands.Add(tailResult);
                }
                operands.AddRange(instruction.Operands.Skip(2));
                instruction.SetOperands(operands);
                instruction.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
            }
            else
            {
                instruction.OpCode = OpCode.Call; // same layout as IndirectCall
                instruction.SetOperand(0, resolved);
            }

            resolver?.RemapRawArguments(instruction, resolved);
            instruction.NativeVirtualDispatch = true;

            // the MethodInfo field is also the same method, name it, for cleanliness and so it can
            // serve as a hidden final parameter if needed
            for (var i = 1; i < instruction.Operands.Count && assembly != null; i++)
            {
                if (SlotLoad(instruction.Operands[i]) is { } methodInfoLoad
                    && ReferenceEquals(methodInfoLoad.Base, klassLocal)
                    && methodInfoLoad.Addend == target.Addend + pointerSize)
                    instruction.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            }

            if (tail)
            {
                var block = method.ControlFlowGraph.Blocks.Single(b=>b.Instructions.Contains(instruction));
                block.AddInstruction(new Instruction(-1,OpCode.Return,
                    method.IsVoid ? [] : new List<IOperand>{tailResult!}));
                block.CalculateBlockType();
            }

            changed = true;
        }

        return changed;

        MemoryOperand? SlotLoad(IOperand operand) => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => inlined,
            LocalVariable local when loads.TryGetValue(local, out var load) => load,
            _ => null
        };
    }

    internal sealed record LateFieldVirtualWitness(LocalVariable Receiver, LocalVariable Klass,
        TypeAnalysisContext ReceiverType, MethodAnalysisContext Target);

    // Unlike the early SSA type fixpoint, this late proof must account for ALL
    // definitions after phi destruction. Never use the last observed load or a
    // guessed local type to license a virtual call.
    internal static LateFieldVirtualWitness? ProveLateFieldVirtualCall(MethodAnalysisContext method,
        Instruction call, RuntimeMetadataLayout layout)
    {
        if (method.ControlFlowGraph is not { } cfg || method.AppContext.Binary.PointerSizeBytes != 8
            || layout.VTable != 0x128 || call.OpCode != OpCode.IndirectCall
            || call.Operands is not [LocalVariable pointer, LocalVariable result, LocalVariable receiver, ..]) return null;
        var writes = cfg.Blocks.SelectMany(b => b.Instructions).Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        if (!writes.TryGetValue(pointer, out var pointerLoad)
            || pointerLoad is not { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [_, MemoryOperand { Base: LocalVariable klass, Index: null, Scale: 0 } slotLoad] }
            || !writes.TryGetValue(klass, out var classLoad)
            || classLoad is not { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [_, MemoryOperand { Base: LocalVariable instance, Addend: 0, Index: null, Scale: 0 }] }
            || !ReferenceEquals(instance, receiver)
            || !writes.TryGetValue(receiver, out var receiverLoad)
            || receiverLoad is not { OpCode: OpCode.Move, NativeReadSize: 8,
                Operands: [_, FieldReference { Parent: null } field] }
            || field.Field.BackingData == null || field.Field.IsStatic || field.Field.Offset < 0
            || field.Field.Offset != field.Field.DefaultOffset || field.Field.Attributes != field.Field.DefaultAttributes
            || !TrivialConstructorRecovery.SameType(field.Field.FieldType, field.Field.DefaultFieldType)
            || field.Offset != field.Field.Offset || field.Field.FieldType is not { IsValueType: false } receiverType
            || receiverType is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or RuntimeClassTypeAnalysisContext
            || receiverType.Definition == null || receiverType.GenericParameters.Count != 0
            || receiver.Type != null && !TrivialConstructorRecovery.SameType(receiver.Type, receiverType)
            || klass.Type != null && (klass.Type is not RuntimeClassTypeAnalysisContext existingClass
                || !TrivialConstructorRecovery.SameType(existingClass.RepresentedType, receiverType))) return null;
        var hierarchy = new HashSet<TypeAnalysisContext>();
        var ownerMatches = false;
        for (var owner = field.Local.Type; owner != null && hierarchy.Add(owner); owner = owner.BaseType)
            if (TrivialConstructorRecovery.SameType(owner, field.Field.DeclaringType)) { ownerMatches = true; break; }
        var receiverBlocks = cfg.Blocks.Where(b => b.Instructions.Contains(receiverLoad)).ToArray();
        if (!ownerMatches || receiverBlocks.Length != 1 || !InlineClassTestRecovery.StableSource(method, field.Local, receiverBlocks[0])
            || !ForwardNullCheckRecovery.DefinitionDominates(cfg, receiverLoad, classLoad)
            || !ForwardNullCheckRecovery.DefinitionDominates(cfg, classLoad, pointerLoad)
            || !ForwardNullCheckRecovery.DefinitionDominates(cfg, pointerLoad, call)) return null;
        var dependencies = new[] { pointer, klass, receiver, field.Local };
        if (cfg.Instructions.Any(i => i.ImplicitDefinition is { } clobbered
            && dependencies.Any(l => l.Register.Number == clobbered.Number && l.Register.Name == clobbered.Name))
            || cfg.Instructions.SelectMany(i => i.Operands).Any(o => EscapesByAddress(o, dependencies))) return null;
        var offset = slotLoad.Addend - layout.VTable;
        if (offset < 0 || offset % 16 != 0 || offset / 16 > int.MaxValue) return null;
        var target = ResolveVTableSlot(method.AppContext, receiverType, (int)(offset / 16));
        // Non-void ordinary calls only: tail/void/HFA/stack ABI shapes require
        // their own proof, not reinterpretation of a stale native result slot.
        if (target == null || target.IsStatic || target.IsVoid || target.GenericParameters.Count != 0
            || target.AppContext.InstructionSet.CallingConventionResolver is not { } resolver
            || resolver.ReturnsViaHiddenBuffer(target)
            || resolver.ResolveForManaged(target).Any(o => o is StackOffset)
            || target.ReturnType is GenericParameterTypeAnalysisContext
            || target.Parameters.Any(p => p.ParameterType is GenericParameterTypeAnalysisContext
                || Arm64HfaLayout.Fields(p.ParameterType) != null)
            || result.Type != null && !TrivialConstructorRecovery.SameType(result.Type, target.ReturnType)) return null;
        return new(receiver, klass, receiverType, target);
    }

    private static bool EscapesByAddress(IOperand operand, LocalVariable[] locals) => operand switch
    {
        AddressOf address => ReferencesLateLocal(address.Target, locals),
        MemoryOperand memory => memory.Base != null && EscapesByAddress(memory.Base, locals)
            || memory.Index != null && EscapesByAddress(memory.Index, locals),
        ArrayAccess array => EscapesByAddress(array.Index, locals),
        _ => false
    };

    private static bool ReferencesLateLocal(IOperand operand, LocalVariable[] locals) => operand switch
    {
        LocalVariable local => locals.Contains(local),
        AddressOf address => ReferencesLateLocal(address.Target, locals),
        MemoryOperand memory => memory.Base != null && ReferencesLateLocal(memory.Base, locals)
            || memory.Index != null && ReferencesLateLocal(memory.Index, locals),
        FieldReference field => locals.Contains(field.Local)
            || field.Parent != null && ReferencesLateLocal(field.Parent, locals),
        ArrayAccess array => locals.Contains(array.Array) || ReferencesLateLocal(array.Index, locals),
        ArrayLength length => locals.Contains(length.Array),
        _ => false
    };

    public static int ResolveLateFieldVirtualCalls(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph == null || method.AppContext.UnityVersion.Major != 2018
            || method.AppContext.UnityVersion.Minor != 4
            || method.AppContext.InstructionSet is not Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet) return 0;
        var layout = RuntimeMetadataLayout.For(method);
        var calls = new Dictionary<Instruction, LateFieldVirtualWitness>();
        foreach (var call in method.ControlFlowGraph.Instructions.ToArray())
            if (ProveLateFieldVirtualCall(method, call, layout) is { } witness) calls[call] = witness;
        foreach (var witness in calls.Values)
        {
            witness.Receiver.Type ??= witness.ReceiverType;
            witness.Klass.Type ??= new RuntimeClassTypeAnalysisContext(witness.ReceiverType, witness.ReceiverType.DeclaringAssembly);
        }
        if (calls.Count == 0 || !ResolveVirtualCalls(method, layout, calls.Keys.ToHashSet())) return 0;
        var count = 0;
        foreach (var (call, witness) in calls)
            if (call.Operands[0] is MethodAnalysisContext actual && ReferenceEquals(actual, witness.Target))
            {
                ((LocalVariable)call.Operands[1]).Type ??= actual.ReturnType;
                count++;
            }
        CallArgumentTrimmer.Run(method);
        DeadCodeEliminator.Run(method);
        return count;
    }

    internal static MethodAnalysisContext? ResolveArrayObjectSlot(ApplicationAnalysisContext app, TypeAnalysisContext type, int slot)
    {
        if (type is not (SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext) || slot < 0) return null;
        var array = app.GetAssemblyByName("mscorlib")?.GetTypeByFullName("System.Array");
        var objectType = app.SystemTypes.SystemObjectType;
        if (array?.Definition == null || objectType.Definition == null
            || slot >= array.Definition.VtableCount || slot >= objectType.Definition.VtableCount) return null;
        var arrayTarget = app.ResolveContextForMethod(array.Definition.VTable[slot]);
        var objectTarget = app.ResolveContextForMethod(objectType.Definition.VTable[slot]);
        // Only slots positively shared with canonical Object. Do not infer an
        // element-specific interface thunk, Array override or hidden generic ABI.
        if (arrayTarget == null || !ReferenceEquals(arrayTarget, objectTarget)
            || !ReferenceEquals(arrayTarget.DeclaringType, objectType) || arrayTarget.IsStatic || arrayTarget.IsVoid
            || arrayTarget.Definition?.slot != slot || arrayTarget.GenericParameters.Count != 0
            || arrayTarget.Parameters.Any(p => p.ParameterType is GenericParameterTypeAnalysisContext)
            || app.InstructionSet.CallingConventionResolver?.ReturnRegister(arrayTarget).Name != "X0") return null;
        return arrayTarget;
    }

    internal static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext, TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;

        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return BindVirtualContext(type,implementation);

        // an abstract method has no implementation, try to resolve it
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
        {
            // Inflated types deliberately do not populate Methods. Abstract
            // slots have no implementation entry, so consult the exact open
            // definition, then reuse the normal owner/arity/type-argument
            // binding. Never infer a declaration by name or drop its arguments.
            if (declarer is GenericInstanceTypeAnalysisContext genericDeclarer)
            {
                var declarations = genericDeclarer.GenericType.Methods
                    .Where(m => m.Definition?.slot == slot).ToArray();
                if (declarations.Length > 1) return null;
                if (declarations.Length == 1)
                    return BindVirtualContext(type, declarations[0]);
                continue;
            }
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return BindVirtualContext(type,declaration);
        }

        return null;
    }

    // A slot on List<long> must not become a call on the open List<T>
    // definition: that loses BOTH parameter and return ABI information.
    internal static MethodAnalysisContext? BindVirtualContext(TypeAnalysisContext receiver,MethodAnalysisContext implementation)
    {
        if(implementation.DeclaringType is not { } owner)return null;
        if(implementation is ConcreteGenericMethodAnalysisContext)
            return implementation; // retain already-instantiated metadata, never guess different arguments
        if(owner.GenericParameters.Count==0)return implementation;
        var seen=new HashSet<TypeAnalysisContext>();
        for(var current=receiver;current!=null && seen.Add(current) && seen.Count<=64;current=current.BaseType)
        {
            if(current is not GenericInstanceTypeAnalysisContext generic || !ReferenceEquals(generic.GenericType,owner))continue;
            if(generic.GenericArguments.Count!=owner.GenericParameters.Count || implementation.GenericParameters.Count!=0)return null;
            return new ConcreteGenericMethodAnalysisContext(implementation,generic.GenericArguments,[]);
        }
        // Keep open definitions as definitions only for their exact open owner.
        return ReferenceEquals(receiver,owner)?implementation:null;
    }

    private static MethodAnalysisContext BaseMethodOf(MethodAnalysisContext method) =>
        method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: { } baseMethod } ? baseMethod : method;

    private static RuntimeMethodInfoAnalysisContext? GetMethodInfoArgument(Instruction call)
    {
        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;

        for (var i = call.Operands.Count - 1; i >= firstArg; i--)
        {
            if (AsMethodInfo(call.Operands[i]) is { } methodInfo)
                return methodInfo;
        }

        return null;
    }

    private static RuntimeMethodInfoAnalysisContext? AsMethodInfo(IOperand operand) =>
        operand switch
        {
            RuntimeMethodInfoAnalysisContext methodInfo => methodInfo,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext methodInfoLocal } => methodInfoLocal,
            _ => null
        };

    private static void HandleKeyFunction(ApplicationAnalysisContext appContext, Instruction instruction, ulong target, BaseKeyFunctionAddresses kFA)
    {
        var method = "";
        if (target == kFA.il2cpp_codegen_initialize_method || target == kFA.il2cpp_codegen_initialize_runtime_metadata)
        {
            if (appContext.MetadataVersion < 27)
            {
                method = nameof(kFA.il2cpp_codegen_initialize_method);
            }
            else
            {
                method = nameof(kFA.il2cpp_codegen_initialize_runtime_metadata);
            }
        }
        else
        {
            var pairs = kFA.Pairs.ToList();
            var key = pairs.FirstOrDefault(pair => pair.Value == target).Key;
            if (key == null)
                return;
            method = key;
        }

        if (method != "")
        {
            instruction.SetOperand(0, new StringLiteral(method));
        }
    }

    // Because of il2cpp fields (like cctor_finished_or_no_cctor) [local @ reg+offset] sometimes can't be resolved, but this works for now
    private static void ResolveGetter(MethodAnalysisContext method)
    {
        if (!method.Name.StartsWith("get_"))
            return;

        // Default get: Return [this @ reg+offset]
        var instructions = method.ControlFlowGraph!.Instructions;
        if (instructions.Count == 1)
        {
            var instr = instructions[0];

            if (instr.OpCode != OpCode.Return
                || instr.Operands.Count < 1
                || instr.Operands[0] is not MemoryOperand memory
                || memory.Index != null || memory.Scale != 0
                || memory.Base is not LocalVariable local)
                return;

            var fieldName = $"<{method.Name[4..]}>k__BackingField";

            var field = method.DeclaringType!.Fields.Find(f => f.Name == fieldName);
            if (field == null)
                return;

            instr.SetOperand(0, new FieldReference(field, local, (int)memory.Addend));
        }
    }
}
