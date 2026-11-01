using System;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class NativeNullableAccessorRecovery
{
    internal static int PrepareStackReceivers(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.PointerSizeBytes != 8
            || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return 0;
        var count = 0;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        foreach (var call in block.Instructions.ToArray())
        {
            if (!call.IsCall || call.Operands[0] is not Immediate target) continue;
            try
            {
                if (!app.Binary.TryMapVirtualAddressToRaw(target.UnsignedValue, out var offset)
                    || offset < 0 || offset > int.MaxValue || offset > app.Binary.RawLength - 8) continue;
                var bytes = app.Binary.GetRawBinaryContent().Slice((int)offset, 8);
                if ((MatchesBody(bytes, true) || MatchesBody(bytes, false))
                    && NativeNullableConstructorRecovery.ScheduleStackReceiver(block, call, requireZeroInitialization: false)) count++;
            }
            catch (Exception) { /* Unproven native bytes never authorize scheduling. */ }
        }
        return count;
    }

    internal static bool MatchesBody(ReadOnlySpan<byte> body, bool hasValue) => body.SequenceEqual(hasValue
        ? new byte[] { 0x00, 0x10, 0x40, 0x39, 0xc0, 0x03, 0x5f, 0xd6 }
        : new byte[] { 0x00, 0x00, 0x40, 0xb9, 0xc0, 0x03, 0x5f, 0xd6 });

    internal static bool TryResolve(MethodAnalysisContext caller, Instruction call,
        Func<ulong, bool, bool>? nativeProof = null)
    {
        var first = call.OpCode == OpCode.Call ? 2 : 1;
        if (!call.IsCall || call.NativeVirtualDispatch || call.Operands[0] is not Immediate target
            || call.Operands.Count < first + 2 || call.Operands.Count > first + 16) return false;
        var info = call.Operands[first + 1] switch
        {
            RuntimeMethodInfoAnalysisContext direct => direct,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext local } => local,
            _ => null
        };
        if (info?.RepresentedMethod is not ConcreteGenericMethodAnalysisContext method
            || method.IsStatic || method.Parameters.Count != 0 || method.MethodGenericParameters.Count != 0
            || method.DeclaringType is not GenericInstanceTypeAnalysisContext owner
            || !NativeNullableConstructorRecovery.OwnerContract(owner)) return false;
        var hasValue = method.Name == "get_HasValue" && method.ReturnType.FullName == "System.Boolean";
        var getValue = method.Name == "GetValueOrDefault"
            && TrivialConstructorRecovery.SameType(method.ReturnType, owner.GenericArguments[0]);
        if (!hasValue && !getValue) return false; // get_Value can throw; never substitute it.
        var graph = caller.ControlFlowGraph!;
        var block = graph.Blocks.SingleOrDefault(b => b.Instructions.Contains(call));
        if (block == null) return false;
        var pointer = call.Operands[first];
        for (var depth = 0; depth < 8 && pointer is LocalVariable local; depth++)
        {
            var definitions = block.Instructions.Take(block.Instructions.IndexOf(call))
                .Where(i => ReferenceEquals(i.Destination, local)).ToArray();
            if (definitions is not [{ OpCode: OpCode.Move, Operands: [_, var source] }]) return false;
            pointer = source;
        }
        if (pointer is not AddressOf { Target: LocalVariable storage }
            || storage.Type != null && !TrivialConstructorRecovery.SameType(storage.Type, owner)) return false;
        if (nativeProof == null)
        {
            var app = caller.AppContext;
            if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.PointerSizeBytes != 8
                || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return false;
            try
            {
                if (!app.Binary.TryMapVirtualAddressToRaw(target.UnsignedValue, out var offset)
                    || offset < 0 || offset > int.MaxValue || offset > app.Binary.RawLength - 8
                    || !MatchesBody(app.Binary.GetRawBinaryContent().Slice((int)offset, 8), hasValue)) return false;
            }
            catch (Exception) { return false; }
        }
        else if (!nativeProof(target.UnsignedValue, hasValue)) return false;
        call.SetOperand(0, method);
        call.SetOperands(call.Operands.Take(first + 2).ToList());
        return true;
    }
}
