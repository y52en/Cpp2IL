using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Bind an unregistered unboxed clone only to its ORIGINAL registered wrapper.
// The exact wrapper is ADD X0,X0,#16; MOV W1,#selector; B target. The clone is
// the same MOV and same absolute B target. No SDK name/fingerprint is accepted
// as an identity. The caller must supply the exact metadata-bound value byref.
internal static class NativeSelectorCloneRecovery
{
    internal readonly record struct Key(uint Selector, ulong Target);
    static readonly ConditionalWeakTable<ApplicationAnalysisContext, Lazy<bool>> Profiles = new();
    static readonly ConditionalWeakTable<ApplicationAnalysisContext, Dictionary<Key, List<MethodAnalysisContext>>> Catalogs = new();

    static bool Supports(ApplicationAnalysisContext app) =>
        app.Binary.PointerSizeBytes == 8 && app.UnityVersion.Major == 2018 && app.UnityVersion.Minor == 4
        && Profiles.GetValue(app, owner => new Lazy<bool>(() => CheckedUnboxRecovery.Supports(owner)
            && owner.Metadata.BaseStream is MemoryStream stream
            && string.Equals(Convert.ToHexString(SHA256.HashData(stream.ToArray())),
                "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e", StringComparison.OrdinalIgnoreCase))).Value;

    internal static bool TryKey(ReadOnlySpan<byte> bytes, ulong address, bool boxed, out Key key)
    {
        key = default; var skip = boxed ? 4 : 0;
        if ((address & 3) != 0 || bytes.Length < skip + 8
            || boxed && BitConverter.ToUInt32(bytes[..4]) != 0x91004000u) return false;
        var move = BitConverter.ToUInt32(bytes.Slice(skip, 4));
        uint selector;
        if (move == 0x2a1f03e1u) selector = 0; // MOV W1,WZR, including canonical get_Year.
        else if ((move & 0xffc003ffu) == 0x320003e1u)
        {
            // MOV W1,#bitmask aliases ORR W1,WZR,#imm. Day/Month use this
            // actual encoding in the authenticated original, not MOVZ.
            var imms = (int)((move >> 10) & 63);
            var immr = (int)((move >> 16) & 63);
            var length = -1;
            for (var bit = 5; bit >= 0; bit--)
                if (((~imms & 63) & (1 << bit)) != 0) { length = bit; break; }
            if (length < 1) return false;
            var size = 1 << length; var levels = size - 1;
            var ones = (imms & levels) + 1;
            if (ones == size) return false;
            var rotation = immr & levels;
            var element = (1UL << ones) - 1;
            var mask = (1UL << size) - 1;
            element = ((element >> rotation) | (element << (size - rotation))) & mask;
            selector = 0;
            for (var offset = 0; offset < 32; offset += size)
                selector |= (uint)(element << offset);
        }
        else
        {
            var opcode = move & 0xff80001fu;
            var shift = (int)((move >> 21) & 3) * 16;
            if (opcode is not (0x52800001u or 0x12800001u) || shift > 16) return false;
            selector = ((move >> 5) & 0xffffu) << shift;
            if (opcode == 0x12800001u) selector = ~selector;
        }
        var branch = BitConverter.ToUInt32(bytes.Slice(skip + 4, 4));
        if ((branch & 0xfc000000u) != 0x14000000u) return false; // B only: not BL or conditional.
        var target = unchecked((ulong)((long)address + skip + 4 + ((long)((int)(branch << 6) >> 6) << 2)));
        if (target >= address && target < address + (ulong)skip + 8) return false;
        key = new(selector, target); return true;
    }

    static byte[]? Read(ApplicationAnalysisContext app, ulong address, int length)
    {
        if (!app.Binary.TryMapVirtualAddressToRaw(address, out var raw)
            || raw < 0 || raw > app.Binary.RawLength - length) return null;
        return app.Binary.GetRawBinaryContent().Slice((int)raw, length).ToArray();
    }

    static bool Eligible(MethodAnalysisContext target)
    {
        if (target.IsStatic || target.GenericParameters.Count != 0 || target.Parameters.Count != 0
            || target.DeclaringType is not { IsValueType: true } owner || owner.HasAnyGenericParameters()
            || owner.IsGenericInstance || target.ReturnType.HasAnyGenericParameters()
            || target.ReturnType.FullName is "System.Void" or "System.Single" or "System.Double"
            // An unresolved direct call captures X0. Never invent a SIMD/HFA
            // result from that integer-return snapshot.
            || target.ReturnType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            || target.ReturnType.IsValueType && !TypeSizes.IsScalarValueType(target.ReturnType)) return false;
        // With <=16 bytes, ADD #16 cannot address an ordinary nested instance
        // field within the value. Its registered entry is the boxed adjustor.
        var size = TypeSizes.UnboxedSize(owner, 8);
        return size is > 0 and <= 16;
    }

    static Dictionary<Key, List<MethodAnalysisContext>> BuildCatalog(ApplicationAnalysisContext app)
    {
        var result = new Dictionary<Key, List<MethodAnalysisContext>>();
        foreach (var method in app.Assemblies.SelectMany(a => a.Types).Where(t => t.Definition != null && t.IsValueType)
                     .SelectMany(t => t.Methods).Where(m => m.Definition != null && m.UnderlyingPointer != 0))
        {
            if (!Eligible(method)) continue;
            var bytes = Read(app, method.UnderlyingPointer, 12);
            if (bytes == null || !TryKey(bytes, method.UnderlyingPointer, true, out var key)
                || !app.Binary.TryMapVirtualAddressToRaw(key.Target, out _)) continue;
            if (!result.TryGetValue(key, out var methods)) result[key] = methods = [];
            if (!methods.Contains(method)) methods.Add(method);
        }
        return result;
    }

    internal static bool TryRewrite(MethodAnalysisContext method, Instruction call,
        IEnumerable<MethodAnalysisContext> candidates, bool authenticatedOriginalImage)
    {
        if (!authenticatedOriginalImage || method.ControlFlowGraph is not {} graph
            || call is not { OpCode: OpCode.Call, NativeVirtualDispatch: false, ImplicitDefinition: null,
                Operands: [Immediate, LocalVariable result, var receiver, ..] }
            || call.NativeDirectCallTarget != ((Immediate)call.Operands[0]).UnsignedValue
            || call.Operands.Skip(3).Any(o => o is not (LocalVariable or Immediate))
            || graph.Blocks.Count(b => b.Instructions.Contains(call)) != 1 || !method.Locals.Contains(result)) return false;
        var owner = receiver switch
        {
            AddressOf { Target: LocalVariable local } when method.Locals.Contains(local) && local.Type?.IsValueType == true => local.Type,
            LocalVariable { Type: ByRefTypeAnalysisContext reference } local when method.Locals.Contains(local) => reference.ElementType,
            _ => null,
        };
        if (owner == null) return false;
        var exact = candidates.Where(Eligible).Where(m => TrivialConstructorRecovery.SameType(owner, m.DeclaringType))
            .Where(m => result.Type == null || TrivialConstructorRecovery.SameType(result.Type, m.ReturnType)).Distinct().ToArray();
        if (exact.Length != 1) return false;
        var target = exact[0];
        // Only already materialized ABI padding is dropped. Earlier effects,
        // byref storage, CFG edges and the actual original native address stay.
        call.SetOperands(target, result, receiver);
        result.Type ??= target.ReturnType;
        return true;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not {} graph) return 0;
        var calls = graph.Instructions.Where(i => i is { OpCode: OpCode.Call,
            Operands: [Immediate, LocalVariable, AddressOf or LocalVariable, ..] }).ToArray();
        if (calls.Length == 0 || !Supports(method.AppContext)) return 0;
        var catalog = Catalogs.GetValue(method.AppContext, BuildCatalog); var count = 0;
        foreach (var call in calls)
        {
            var address = ((Immediate)call.Operands[0]).UnsignedValue;
            var bytes = Read(method.AppContext, address, 8);
            if (bytes != null && TryKey(bytes, address, false, out var key)
                && catalog.TryGetValue(key, out var candidates)
                && TryRewrite(method, call, candidates, true)) count++;
        }
        return count;
    }
}
