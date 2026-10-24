using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>Recover a bound virtual delegate from the MethodInfo half of a verified vtable slot.</summary>
public static class VirtualDelegateRecovery
{
    public static int Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.UnityVersion.Major != 2018 || method.AppContext.UnityVersion.Minor != 4)
            return 0;
        return Run(method, RuntimeMetadataLayout.For(method));
    }

    internal static int Run(MethodAnalysisContext method, RuntimeMetadataLayout layout)
    {
        if (method.ControlFlowGraph is not { } graph || method.IsStatic
            || method.AppContext.Binary.PointerSizeBytes != 8 || layout.VTable != 0x128) return 0;
        var instructions = graph.Instructions.ToArray();
        var writes = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToArray());
        var changed = 0;
        foreach (var load in instructions)
        {
            if (load is not { OpCode: OpCode.Move, NativeReadSize: 8,
                    Operands: [LocalVariable { Type.FullName: "System.IntPtr" } pointer,
                        MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext klassType } klass,
                            Index: null, Scale: 0 } memory] }
                || !writes.TryGetValue(pointer, out var pointerWrites) || pointerWrites.Length != 1
                || !writes.TryGetValue(klass, out var klassWrites) || klassWrites.Length != 1
                || klassWrites[0] is not { OpCode: OpCode.Move, NativeReadSize: 8,
                    Operands: [_, MemoryOperand { Base: LocalVariable receiver, Addend: 0, Index: null, Scale: 0 }] }
                // This first profile deliberately admits only the immutable canonical
                // incoming this. Nullable/field/phi receivers need a separate timing proof.
                || !receiver.IsThis || !method.ParameterLocals.Contains(receiver) || writes.ContainsKey(receiver)
                || receiver.Type is not { IsValueType: false, GenericParameters.Count: 0 } receiverType
                || receiverType is GenericInstanceTypeAnalysisContext
                || !TrivialConstructorRecovery.SameType(receiverType, method.DeclaringType!)
                || !TrivialConstructorRecovery.SameType(receiverType, klassType.RepresentedType)
                || instructions.Any(i => i.Operands.Any(o => AddressEscapes(o, receiver, klass, pointer)))) continue;

            var offset = memory.Addend - layout.VTable - 8;
            if (offset < 0 || offset % 16 != 0 || offset / 16 > int.MaxValue) continue;
            var target = MetadataResolver.ResolveVTableSlot(method.AppContext, receiverType, (int)(offset / 16));
            if (target is not { IsVirtual: true, IsStatic: false, GenericParameters.Count: 0 }
                || target.ReturnType.HasAnyGenericParameters()
                || target.Parameters.Any(p => p.ParameterType.HasAnyGenericParameters())) continue;

            var consumers = instructions.Where(i => !ReferenceEquals(i, load)
                && i.Operands.Any(o => Uses(o, pointer))).ToArray();
            if (consumers.Length != 1 || consumers[0] is not { OpCode: OpCode.CallVoid,
                    Operands: [MethodAnalysisContext { Name: ".ctor", IsStatic: false,
                        DeclaringType: { IsDelegate: true } delegateType } constructor,
                        LocalVariable delegateObject, LocalVariable boundReceiver, LocalVariable argument] } call
                || !ReferenceEquals(boundReceiver, receiver) || !ReferenceEquals(argument, pointer)
                || delegateObject.Type == null || !TrivialConstructorRecovery.SameType(delegateObject.Type, delegateType)
                || constructor.Parameters.Count != 2
                || constructor.Parameters[0].ParameterType.FullName != "System.Object"
                || constructor.Parameters[1].ParameterType.FullName != "System.IntPtr"
                || !ForwardNullCheckRecovery.DefinitionDominates(graph, klassWrites[0], load)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph, load, call)) continue;
            var invoke = DelegateInvoke(delegateType);
            if (invoke == null || !TrivialConstructorRecovery.SameType(invoke.ReturnType, target.ReturnType)
                || invoke.Parameters.Count != target.Parameters.Count
                || invoke.Parameters.Where((p, i) => !TrivialConstructorRecovery.SameType(
                    p.ParameterType, target.Parameters[i].ParameterType)).Any()) continue;

            if (!writes.TryGetValue(delegateObject, out var allocations) || allocations.Length != 1
                || allocations[0] is not { OpCode: OpCode.Newobj, Operands: [_, TypeAnalysisContext allocatedType] } allocation
                || !TrivialConstructorRecovery.SameType(allocatedType, delegateType)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph, allocation, load)
                || !ForwardNullCheckRecovery.DefinitionDominates(graph, allocation, call)
                || instructions.Any(i => !ReferenceEquals(i, allocation) && !ReferenceEquals(i, call)
                    && i.Operands.Any(o => Uses(o, delegateObject))
                    && !ForwardNullCheckRecovery.DefinitionDominates(graph, call, i))) continue;

            // Only immutable NONNULL incoming this: virtual lookup is pure and
            // the runtime delegate ctor has exactly its standard bound shape.
            // Fuse at the original allocation, not by passing a future local
            // into IlGenerator's general earlier-allocation constructor fusion.
            allocation.OpCode = OpCode.NewVirtualDelegate;
            allocation.SetOperands(delegateObject, constructor, target, receiver);
            load.OpCode = OpCode.Nop; load.SetOperands();
            call.OpCode = OpCode.Nop; call.SetOperands();
            changed++;
        }
        return changed;
    }

    private static MethodAnalysisContext? DelegateInvoke(TypeAnalysisContext delegateType)
    {
        // Referenced closed contexts intentionally do not duplicate the owner's
        // Methods collection. Bind its ONE actual Invoke definition using the
        // exact metadata arguments, never infer them from the target method.
        var definition = delegateType is GenericInstanceTypeAnalysisContext closed ? closed.GenericType : delegateType;
        var invokes = definition.Methods.Where(m => m.Name == "Invoke" && !m.IsStatic).ToArray();
        if (invokes.Length != 1 || invokes[0].GenericParameters.Count != 0) return null;
        if (delegateType is not GenericInstanceTypeAnalysisContext generic) return invokes[0];
        if (generic.GenericArguments.Count != definition.GenericParameters.Count
            || generic.GenericArguments.Count == 0 || generic.GenericArguments.Any(t => t.HasAnyGenericParameters())) return null;
        return new ConcreteGenericMethodAnalysisContext(invokes[0], generic.GenericArguments, []);
    }

    private static bool AddressEscapes(IOperand operand, params LocalVariable[] values)
        => operand switch
        {
            AddressOf address => values.Any(v => Uses(address.Target, v)),
            MemoryOperand memory => memory.Base != null && AddressEscapes(memory.Base, values)
                || memory.Index != null && AddressEscapes(memory.Index, values),
            _ => false
        };

    private static bool Uses(IOperand operand, LocalVariable value)
        => ReferenceEquals(operand, value) || operand switch
        {
            MemoryOperand memory => memory.Base != null && Uses(memory.Base, value)
                || memory.Index != null && Uses(memory.Index, value),
            AddressOf address => Uses(address.Target, value),
            FieldReference field => ReferenceEquals(field.Local, value)
                || field.Parent != null && Uses(field.Parent, value),
            ArrayAccess access => Uses(access.Array, value) || Uses(access.Index, value),
            ArrayLength length => Uses(length.Array, value),
            _ => false
        };
}
