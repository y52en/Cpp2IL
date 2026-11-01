using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Utils;
using LibCpp2IL;
using LibCpp2IL.Metadata;
using StableNameDotNet.Providers;

namespace Cpp2IL.Core.Model.Contexts;

/// <summary>
/// Represents one method within the application. Can be analyzed to attempt to reconstruct the function body.
/// </summary>
public class MethodAnalysisContext : HasGenericParameters, IMethodInfoProvider, ISIL.IOperand
{
    /// <summary>
    /// The underlying metadata for the method.
    ///
    /// Nullable iff this is a subclass.
    /// </summary>
    public readonly Il2CppMethodDefinition? Definition;

    /// <summary>
    /// The analysis context for the declaring type of this method.
    /// </summary>
    public readonly TypeAnalysisContext? DeclaringType;

    /// <summary>
    /// The address of this method as defined in the underlying metadata.
    /// </summary>
    public virtual ulong UnderlyingPointer => Definition?.MethodPointer ?? throw new("Subclasses of MethodAnalysisContext should override UnderlyingPointer");

    public ulong Rva => UnderlyingPointer == 0 ? 0 : AppContext.Binary.GetRva(UnderlyingPointer);

    /// <summary>
    /// The raw method body as machine code in the active instruction set.
    /// </summary>
    public BinarySlice RawBytes = BinarySlice.Empty;

    /// <summary>
    /// The first-stage-analyzed Instruction-Set-Independent Language Instructions.
    /// </summary>
    public List<Instruction>? ConvertedIsil;

    /// <summary>
    /// All ISIL local variables.
    /// </summary>
    public List<LocalVariable> Locals = [];

    /// <summary>
    /// Operands used as parameters.
    /// </summary>
    public List<ISIL.IOperand> ParameterOperands = [];

    /// <summary>
    /// The control flow graph for this method, if one is built.
    /// </summary>
    public ISILControlFlowGraph? ControlFlowGraph;

    /// <summary>
    /// Dominance info for the control flow graph.
    /// </summary>
    public DominatorInfo? DominatorInfo;

    public List<string> AnalysisWarnings = [];

    public static int MaxMethodSizeBytes = 30000; // 30KB

    public List<ParameterAnalysisContext> Parameters = [];

    public List<LocalVariable> ParameterLocals = [];

    /// <summary>
    /// Does this method return void?
    /// </summary>
    public bool IsVoid => ReturnType == AppContext.SystemTypes.SystemVoidType;

    public bool IsStatic => (Attributes & MethodAttributes.Static) != 0;

    public bool IsVirtual => (Attributes & MethodAttributes.Virtual) != 0;

    public bool IsAbstract => (Attributes & MethodAttributes.Abstract) != 0;

    public bool IsNewSlot => (Attributes & MethodAttributes.NewSlot) != 0;

    public bool IsFinal => (Attributes & MethodAttributes.Final) != 0;

    protected override int CustomAttributeIndex => Definition?.customAttributeIndex ?? throw new("Subclasses of MethodAnalysisContext should override CustomAttributeIndex if they have custom attributes");

    public override AssemblyAnalysisContext CustomAttributeAssembly => DeclaringType?.DeclaringAssembly ?? throw new("Subclasses of MethodAnalysisContext should override CustomAttributeAssembly if they have custom attributes");

    public override string DefaultName => Definition?.Name ?? throw new("Subclasses of MethodAnalysisContext should override DefaultName");

    public string FullName => DeclaringType == null ? Name : $"{DeclaringType.FullName}::{Name}";

    public string FullNameWithSignature => $"{ReturnType.FullName} {FullName}({string.Join(", ", Parameters.Select(p => p.HumanReadableSignature))})";

    public virtual MethodAttributes DefaultAttributes => Definition?.Attributes ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultAttributes)}");

    public virtual MethodAttributes? OverrideAttributes { get; set; }

    public MethodAttributes Attributes
    {
        get => OverrideAttributes ?? DefaultAttributes;
        set => OverrideAttributes = value;
    }

    public virtual MethodImplAttributes DefaultImplAttributes => Definition?.MethodImplAttributes ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultImplAttributes)}");

    public virtual MethodImplAttributes? OverrideImplAttributes { get; set; }

    public MethodImplAttributes ImplAttributes
    {
        get => OverrideImplAttributes ?? DefaultImplAttributes;
        set => OverrideImplAttributes = value;
    }

    public MethodAttributes Visibility
    {
        get
        {
            return Attributes & MethodAttributes.MemberAccessMask;
        }
        set
        {
            Attributes = (Attributes & ~MethodAttributes.MemberAccessMask) | (value & MethodAttributes.MemberAccessMask);
        }
    }

    private List<GenericParameterTypeAnalysisContext>? _genericParameters;
    public override List<GenericParameterTypeAnalysisContext> GenericParameters
    {
        get
        {
            // Lazy load the generic parameters
            _genericParameters ??= Definition?.GenericContainer?.GenericParameters.Select(p => new GenericParameterTypeAnalysisContext(p, this)).ToList() ?? [];
            return _genericParameters;
        }
    }

    private ushort Slot => Definition?.slot ?? ushort.MaxValue;

    public virtual TypeAnalysisContext DefaultReturnType => AppContext.ResolveIl2CppType(Definition?.RawReturnType) ?? throw new($"Subclasses of MethodAnalysisContext should override {nameof(DefaultReturnType)}");

    public TypeAnalysisContext? OverrideReturnType { get; set; }

    //TODO Support custom attributes on return types (v31 feature)
    public TypeAnalysisContext ReturnType
    {
        get => OverrideReturnType ?? DefaultReturnType;
        set => OverrideReturnType = value;
    }

    public MethodAnalysisContext? BaseMethod
    {
        get
        {
            if (Definition == null)
                return null;

            var vtable = DeclaringType?.Definition?.VTable;
            if (vtable == null)
                return null;

            for (var i = 0; i < vtable.Length; ++i)
            {
                var vtableEntry = vtable[i];
                if (vtableEntry is null or { Type: not MetadataUsageType.MethodDef } || vtableEntry.AsMethod() != Definition)
                    continue;

                if (IsInterfaceSlot(this, i))
                {
                    continue;
                }

                var baseType = DeclaringType?.DefaultBaseType;
                while (baseType is not null)
                {
                    if (TryGetMethodForSlot(baseType, i, out var method))
                    {
                        return method;
                    }
                    baseType = baseType.DefaultBaseType;
                }
            }
            return null;
        }
    }

    private List<MethodAnalysisContext>? _overrides;

    /// <summary>
    /// The set of interface methods which this method explicitly overrides.
    /// </summary>
    public List<MethodAnalysisContext> Overrides
    {
        get
        {
            // Lazy load the overrides
            return _overrides ??= GetOverrides().ToList();
        }
    }

    private IEnumerable<MethodAnalysisContext> GetOverrides()
    {
        if (Definition == null)
            return [];

        var declaringTypeDefinition = DeclaringType?.Definition;
        if (declaringTypeDefinition == null)
            return [];

        var vtable = declaringTypeDefinition.VTable;
        if (vtable == null)
            return [];

        return GetOverriddenMethods(declaringTypeDefinition, vtable);

        IEnumerable<MethodAnalysisContext> GetOverriddenMethods(Il2CppTypeDefinition declaringTypeDefinition, MetadataUsage?[] vtable)
        {
            for (var i = 0; i < vtable.Length; ++i)
            {
                var vtableEntry = vtable[i];
                if (vtableEntry is null or { Type: not MetadataUsageType.MethodDef })
                    continue;

                if (vtableEntry.AsMethod() != Definition)
                    continue;

                // Interface inheritance
                foreach (var interfaceOffset in declaringTypeDefinition.InterfaceOffsets)
                {
                    if (i >= interfaceOffset.offset)
                    {
                        var interfaceTypeContext = AppContext.ResolveIl2CppType(interfaceOffset.Type);
                        var slot = i - interfaceOffset.offset;
                        if (TryGetMethodForSlot(interfaceTypeContext, slot, out var method) && !IsInterfaceSlot(method, slot))
                        {
                            yield return method;
                        }
                    }
                }
            }
        }
    }

    private static bool IsInterfaceSlot(MethodAnalysisContext method, int slot)
    {
        var declaringTypeDefinition = method.DeclaringType?.Definition;
        if (declaringTypeDefinition == null)
            return false;

        foreach (var interfaceOffset in declaringTypeDefinition.InterfaceOffsets)
        {
            if (slot >= interfaceOffset.offset)
            {
                var interfaceTypeContext = method.AppContext.ResolveIl2CppType(interfaceOffset.Type);
                if (HasMethodForSlot(interfaceTypeContext, slot - interfaceOffset.offset))
                {
                    return true;
                }
            }
        }
        return false;
    }

    private static bool HasMethodForSlot(TypeAnalysisContext declaringType, int slot)
    {
        if (declaringType is GenericInstanceTypeAnalysisContext genericInstanceType)
        {
            return genericInstanceType.GenericType.Methods.Any(m => m.Slot == slot);
        }
        else
        {
            return declaringType.Methods.Any(m => m.Slot == slot);
        }
    }

    private static bool TryGetMethodForSlot(TypeAnalysisContext declaringType, int slot, [NotNullWhen(true)] out MethodAnalysisContext? method)
    {
        if (declaringType is GenericInstanceTypeAnalysisContext genericInstanceType)
        {
            var genericMethod = genericInstanceType.GenericType.Methods.FirstOrDefault(m => m.Slot == slot);
            if (genericMethod is not null)
            {
                method = new ConcreteGenericMethodAnalysisContext(genericMethod, genericInstanceType.GenericArguments, []);
                return true;
            }
        }
        else
        {
            var baseMethod = declaringType.Methods.FirstOrDefault(m => m.Slot == slot);
            if (baseMethod is not null)
            {
                method = baseMethod;
                return true;
            }
        }

        method = null;
        return false;
    }

    public MethodAnalysisContext(Il2CppMethodDefinition? definition, TypeAnalysisContext parent) : base(definition?.token ?? 0, parent.AppContext)
    {
        DeclaringType = parent;
        Definition = definition;

        if (Definition != null)
        {
            InitCustomAttributeData();

            for (var i = 0; i < Definition.InternalParameterData!.Length; i++)
            {
                var parameterDefinition = Definition.InternalParameterData![i];
                Parameters.Add(new(parameterDefinition, i, this));
            }
        }
    }

    public void EnsureRawBytes()
    {
        //Some abstract methods (on interfaces, no less) apparently have a body? Unity doesn't support default interface methods so idk what's going on here.
        //E.g. UnityEngine.Purchasing.AppleCore.dll: UnityEngine.Purchasing.INativeAppleStore::SetUnityPurchasingCallback on among us (itch.io build)
        if (UnderlyingPointer != 0 && !DefaultAttributes.HasFlag(MethodAttributes.Abstract))
        {
            RawBytes = AppContext.InstructionSet.GetRawBytesForMethod(this, this is AttributeGeneratorMethodAnalysisContext);

            if (RawBytes.Length == 0)
            {
                Logger.VerboseNewline("\t\t\tUnexpectedly got 0-byte method body for " + this + $". Pointer was 0x{UnderlyingPointer:X}", "MAC");
            }
        }
    }

    protected MethodAnalysisContext(ApplicationAnalysisContext context) : base(0, context)
    { }

    [MemberNotNull(nameof(ConvertedIsil))]
    public void Analyze()
    {
        void TraceAnalysis(string stage)
        {
            var requested = Environment.GetEnvironmentVariable("CPP2IL_TRACE_ANALYSIS_RVAS");
            if (requested == null || !requested.Split(',').Any(value => string.Equals(value.Trim(),
                    UnderlyingPointer.ToString("X"), StringComparison.OrdinalIgnoreCase))) return;
            Console.Error.WriteLine("ANALYSIS_STAGE " + stage + " " + FullName);
            foreach (var block in ControlFlowGraph!.Blocks)
            {
                Console.Error.WriteLine("BLOCK " + block.ID + " PREDECESSORS "
                    + string.Join(",", block.Predecessors.Select(b => b.ID)));
                foreach (var instruction in block.Instructions) Console.Error.WriteLine(instruction);
            }
        }
        if (MaxMethodSizeBytes != -1 && RawBytes.Length > MaxMethodSizeBytes)
        {
            Logger.WarnNewline($"Method {FullName} is too big ({RawBytes.Length} bytes), skipping analysis.");
            ConvertedIsil = [];
            return;
        }

        if (ConvertedIsil != null)
            return;

        if (UnderlyingPointer == 0)
        {
            ConvertedIsil = [];
            return;
        }

        ConvertedIsil = AppContext.InstructionSet.GetIsilFromMethod(this);
        ParameterOperands = AppContext.InstructionSet.GetParameterOperandsFromMethod(this);

        if (ConvertedIsil.Count == 0)
            return; //Nothing to do, empty function

        ControlFlowGraph = new ISILControlFlowGraph(ConvertedIsil);

        // Indirect jumps/calls should probably be resolved here before stack analysis

        NativeStoreLeafExpansion.Run(this);
        NativeFloatingLoadLeafExpansion.Run(this);
        NativeIntegerLoadLeafExpansion.Run(this);
        StackAnalyzer.Analyze(this);
        InlineBoxedHfaRecovery.Run(this);
        NativeNullableConstructorRecovery.PrepareStackReceivers(this);
        NativeNullableAccessorRecovery.PrepareStackReceivers(this);
        NativeScalarStoreRecovery.Run(this);
        Arm64HfaRecovery.Run(this);
        Arm64IntegerReturnCopyRecovery.Run(this);
        HiddenStructReturnRecovery.Run(this);
        WholeStackValueCopyRecovery.Run(this);
        WholeStructInitializationRecovery.Run(this);
        AddressedStackFieldStoreRecovery.Run(this);
        BoxAddressRecovery.Run(this);
        TraceAnalysis("stack-recovered");

        // Dominator info must be computed after stack analysis, which removes unreachable/empty
        // blocks and would otherwise leave the dominator tree out of sync with the graph SSA sees.
        DominatorInfo = new DominatorInfo(ControlFlowGraph);

        // Create locals
        SsaForm.Build(this);
        LocalVariables.CreateAll(this);
        TraceAnalysis("ssa-locals");
        NativeWord32IdentityRecovery.Run(this);

        // Fold the explicit per-comparison flag arithmetic back into single relational comparisons,
        // then eliminate the now-dead flag computations. Both run in SSA form, where each
        // flag/temporary has a single, version-stable definition.
        FlagConditionRecovery.Run(this);
        DeadCodeEliminator.Run(this);

        // Resolve call targets, strings and getters, then run the combined type-propagation and
        // field-resolution fixpoint - all while still in SSA form, so every local is
        // single-assignment and a type, once known, is stable for that value.
        MetadataResolver.ResolveAll(this);

        // Resolve KeyFunctionAddress calls, then collect what removing the write barriers left dead.
        KeyFunctionRecovery.Run(this);
        DeadCodeEliminator.Run(this);

        // Delete any il2cpp_codegen_initialize_runtime_metadata/il2cpp_codegen_initialize_method
        MetadataInitGuardRemover.Run(this);
        MetadataInitForkRecovery.Run(ControlFlowGraph!);

        // Delete inlined GC write barriers
        WriteBarrierRecovery.Run(this);

        InjectedCheckRemover.Run(this);

        ArrayRecovery.RecoverAllocationsOnly(this);
        InterfaceInvokerThunkRecovery.Run(this);
        AllocatedObjectArrayHelperRecovery.TrimKnownHelperPadding(this);
        AllocatedObjectArrayHelperRecovery.Run(this);
        ForwardNullCheckRecovery.Run(this);
        if(RuntimeHelperArgumentPaddingRecovery.Run(this)>0)DeadCodeEliminator.Run(this);
        // Preserve early dispatch binding before stale raw return registers
        // can acquire a managed type from a later use of the same native bank.
        var interfaceDispatchState=InterfaceDispatchRecovery.RunWithState(this);
        LocalVariables.ResolveTypesAndFields(this);

        // Interface cleanup also needs the managed receiver/vtable identities:
        // a previous virtual call's MethodInfo can survive into its merge phis.
        InterfaceDispatchRecovery.RunWithState(this,interfaceDispatchState);
        LocalVariables.ResolveTypesAndFields(this);
        TraceAnalysis("typed");

        if (Arm64AtomicCompareExchangeRecovery.Run(this) > 0)
            LocalVariables.ResolveTypesAndFields(this);

        // W0 is a scalar view of a metadata-proven small aggregate return;
        // do not let a whole managed struct reach a native-width comparison.
        if (Arm64AggregateReturnLowWordRecovery.Run(this) > 0)
            LocalVariables.ResolveTypesAndFields(this);

        // Optional full-FDE masked accessor evidence is receiver-sensitive;
        // never register these equivalent functions as global address aliases.
        NativeMaskedAccessorRecovery.Run(this);
        NativeIntegerAccessorRecovery.Run(this);

        // Managed signatures now type input arguments and resolved call results.
        // Revisit only the hash-proven outlined helpers while definitions are
        // still SSA; the first pass must decline those initially untyped values.
        AllocatedObjectArrayHelperRecovery.Run(this);
        ForwardNullCheckRecovery.Run(this);

        // Boolean Not/copy wrappers cannot safely be followed until types are resolved.
        InjectedCheckRemover.Run(this);

        // Needs the MethodInfo* receivers typed, so runs after resolution unlike the class-init guards
        MetadataInitGuardRemover.RunRgctx(this);

        MetadataInitGuardRemover.RewriteUnguardedInits(this);

        // Needs type resolved for delegate locals
        DelegateInvokeRecovery.Run(this);
        BooleanFlagSimplifier.Run(this);
        DeadCodeEliminator.Run(this);

        // Copy/constant propagation belongs in SSA, where one definition dominates all uses and phis
        // make joins explicit, so forwarding a value is an unconditional global substitution.
        if (PhiMemoryLoadRecovery.Run(this) > 0)
        {
            // The per-edge reads did not exist during ResolveAll. Resolve exact
            // original metadata globals before their pointer phis are removed.
            MetadataResolver.ResolveMetadataUsages(this);
            LocalVariables.ResolveTypesAndFields(this);
        }
        TypedStructZeroRecovery.Run(this);
        SsaSimplifier.Run(this);

        // Folding a constant exposes more to propagate
        for (var i = 0; i < 8 && ConstantFolder.Run(this); i++)
            SsaSimplifier.Run(this);

        // A proven vector zero may become an immediate only after these copy
        // folds. Recheck the same native byte-coverage/metadata-layout proof.
        TypedStructZeroRecovery.Run(this);

        if (SsaFieldAddressRecovery.Run(this) > 0)
            LocalVariables.ResolveTypesAndFields(this);
        if (NativeScalarValueRecovery.Run(this) > 0)
            LocalVariables.ResolveTypesAndFields(this);
        InternalCallGuardRemover.Run(this);
        KeyFunctionRecovery.Run(this);

        // Type/copy resolution can expose pure loop-carried cycles which have
        // no path to any observable use. Eliminate them while still in SSA.
        DeadCodeEliminator.Run(this);

        // Dispatch resolution and SSA cleanup can make a previously live
        // native helper return/pointer-loading chain dead. Recheck the SAME
        // fingerprint and next-callvirt proof before destroying SSA identities.
        ForwardNullCheckRecovery.Run(this);

        SsaForm.Remove(this);
        TraceAnalysis("ssa-removed");

        // Phi removal leaves a copy per merged version, most of which can share one local
        CopyCoalescer.Run(this);
        TraceAnalysis("copies-coalesced");

        // Now out of SSA: clean up the per-edge copies that phi removal introduced (a local can have
        // several definitions merging at a join here, so this pass propagates conservatively), then
        // drop dead locals.
        Simplifier.Simplify(this);
        TraceAnalysis("post-ssa-simplified");
        LateMetadataAllocationRecovery.Run(this);

        // Fix float literals
        ReadOnlyScalarRecovery.Run(this);
        // Split the complete native write before converting its low lane into
        // a floating literal. Otherwise a float-first packed store loses the
        // upper fields and no longer matches the bit-preserving splitter.
        PackedScalarConstantStoreRecovery.Run(this);
        FloatLiteralRecovery.Run(this);
        PackedConstantFieldStoreRecovery.Run(this);

        // Runs late so the array type and length reach the allocation call as operands after copy propagation has inlined them
        ArrayRecovery.Run(this);

        LocalVariables.TypeAddressedLocals(this);

        NativeWord32LoopRecovery.Run(this);

        NativeAggregateReturnRecovery.Run(this);
        NativeLocalZeroInitializationRecovery.Run(this);
        NativeByRefAggregateCopyRecovery.Run(this);

        // Copy/stack recovery can expose &DateTime (or another exact value
        // receiver) only now. Keep the identical FDE/type/accessor proof.
        NativeMaskedAccessorRecovery.Run(this);
        NativeIntegerAccessorRecovery.Run(this);

        ConstantBranchFolder.Run(this);

        // Near-last, as it depends on the final block layout
        EqualityBranchInverter.Run(this);

        // Every call that was going to resolve now has. Any argument registers it ended up
        // not using are just keeping their definitions alive, so drop them.
        CallArgumentTrimmer.Run(this);
        NativeMemoryBarrierRecovery.Run(this);
        VirtualDelegateRecovery.Run(this);
        HiddenBufferConstructorReturnRecovery.Run(this);
        // Native receivers still contain pointer copies during the early type
        // fixpoint. Copy propagation exposes &stack storage only later; recover
        // its independently named scalar reads before they become default IL
        // locals and before inlined constructor matching consumes those reads.
        StackFieldRecovery.Run(this);
        StackFieldZeroRecovery.Run(this);
        NativeIndirectValueArgumentRecovery.Run(this);
        DeadCodeEliminator.Run(this);

        // Native argument padding and unused flags must be gone before proving
        // that the cast lookup/exception path has no escaping definitions.
        LateClassInitRecovery.Run(this);
        EquivalentEdgeCopyRecovery.Run(this);
        InlineClassCastRecovery.Run(this);
        RuntimeCheckedCastRecovery.Run(this);
        NullBypassRuntimeCastRecovery.Run(this);
          DominatedRuntimeCastRecovery.Run(this);
        SealedClassCastRecovery.Run(this);
        InlineClassTestRecovery.Run(this);
        SharedClassTestRecovery.Run(this);
        NullEdgeValueRecovery.Run(this);
        MetadataResolver.ResolveLateFieldVirtualCalls(this);
        CovariantArrayStoreRecovery.Run(this);
        AllocatedArrayElementClassRecovery.Run(this);
        EmptyRuntimeGuardRecovery.Run(this);
        ArrayRecovery.RecoverLateSplitLoads(this);
        if (SsaFieldAddressRecovery.Run(this) > 0)
        {
            MetadataResolver.ResolveFieldOffsets(this);
            DeadCodeEliminator.Run(this);
        }
        NativeScalarStorageRecovery.Run(this);
        SharedEnumDefaultReturnRecovery.Run(this);

        // Only now have class-init guards and unused native argument padding
        // disappeared. The complete-copy proof must see the final live graph;
        // it must never ignore unclassified instructions to force a match.
        if (GenericUnboxFieldCopyRecovery.Run(this))
            DeadCodeEliminator.Run(this);
        if (GenericUnboxArrayCopyRecovery.Run(this))
            DeadCodeEliminator.Run(this);

        // Late field/copy and exact call binding can expose the immediate
        // managed dereference only now. Recheck NULL proofs only; do not
        // generalize bounds predicates or erase arbitrary application guards.
        SharedGenericFieldGetterRecovery.Run(this);
        SharedGenericFieldSetterRecovery.Run(this);
        InjectedCheckRemover.RunNullOnly(this);
        NativeArrayBoundsRecovery.Run(this);
        PrimitiveByRefStorageRecovery.Run(this);
        PackedPrimitiveFieldCopyRecovery.Run(this);
        PackedScalarConstantStoreRecovery.Run(this);
        NativePublicFieldAccessorRecovery.Run(this);
        NativeAggregateFieldAccessorRecovery.Run(this);
        NativeSelectorCloneRecovery.Run(this);
        LateScalarTypeRecovery.Run(this);
        SignedConstantDivisionRecovery.Run(this);
        LocalVariables.RemoveUnused(this);
    }

    public void AddWarning(string warning) => AnalysisWarnings.Add(warning);

    public void ReleaseAnalysisData()
    {
        ConvertedIsil = null;
        ControlFlowGraph = null;
        DominatorInfo = null;
    }

    public ConcreteGenericMethodAnalysisContext MakeGenericInstanceMethod(params IEnumerable<TypeAnalysisContext> methodGenericParameters)
    {
        if (this is ConcreteGenericMethodAnalysisContext methodOnGenericInstanceType)
        {
            return new ConcreteGenericMethodAnalysisContext(methodOnGenericInstanceType.BaseMethodContext, methodOnGenericInstanceType.TypeGenericParameters, methodGenericParameters);
        }
        else
        {
            return new ConcreteGenericMethodAnalysisContext(this, [], methodGenericParameters);
        }
    }

    public ConcreteGenericMethodAnalysisContext MakeConcreteGenericMethod(IEnumerable<TypeAnalysisContext> typeGenericParameters, IEnumerable<TypeAnalysisContext> methodGenericParameters)
    {
        if (this is ConcreteGenericMethodAnalysisContext)
        {
            throw new InvalidOperationException($"Attempted to make a {nameof(ConcreteGenericMethodAnalysisContext)} concrete: {this}");
        }
        else
        {
            return new ConcreteGenericMethodAnalysisContext(this, typeGenericParameters, methodGenericParameters);
        }
    }

    public override string ToString() => $"Method: {FullName}";

    #region StableNameDot implementation

    ITypeInfoProvider IMethodInfoProvider.ReturnType =>
        Definition!.RawReturnType!.ThisOrElementIsGenericParam()
            ? new GenericParameterTypeInfoProviderWrapper(Definition.RawReturnType!.GetGenericParamName())
            : TypeAnalysisContext.GetSndnProviderForType(AppContext, Definition!.RawReturnType);

    IEnumerable<IParameterInfoProvider> IMethodInfoProvider.ParameterInfoProviders => Parameters;

    string IMethodInfoProvider.MethodName => Name;

    MethodAttributes IMethodInfoProvider.MethodAttributes => Attributes;

    MethodSemantics IMethodInfoProvider.MethodSemantics
    {
        get
        {
            if (DeclaringType != null)
            {
                //This one is a bit trickier, as il2cpp doesn't use semantics.
                foreach (var prop in DeclaringType.Properties)
                {
                    if (prop.Getter == this)
                        return MethodSemantics.Getter;
                    if (prop.Setter == this)
                        return MethodSemantics.Setter;
                }

                foreach (var evt in DeclaringType.Events)
                {
                    if (evt.Adder == this)
                        return MethodSemantics.AddOn;
                    if (evt.Remover == this)
                        return MethodSemantics.RemoveOn;
                    if (evt.Invoker == this)
                        return MethodSemantics.Fire;
                }
            }

            return 0;
        }
    }

    #endregion
}
