using System;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Reviewed Unity 2018.4 ARM64 profile. The whole image identity, not an RVA or
// guessed helper name alone, authenticates the null check, element-class check,
// InvalidCastException transport and tail-return of object+two pointer words.
// Complete Ghidra evidence: restoration report checked-unbox-round213.
public static class CheckedUnboxRecovery
{
    // Proven boxed-data provenance, distinct from ordinary ref/out parameters.
    internal sealed class UnboxedReference(TypeAnalysisContext type) : ByRefTypeAnalysisContext(type);
    private const ulong CheckedUnboxAddress = 0xA61E70;
    // LibCpp2IL writes ELF relocations during loading. This complete relocated
    // image hash was reproduced in two fresh processes from original file SHA
    // 6bda601c39e4aaede3e4b09d79a0fcc0491606eb01e45fe5a89a1c2e3cc1af26.
    private const string ImageHash = "1a5b36ef24266d5911158725cf70b03ca88961505da606ff0455e0ef83c524d1";
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, Lazy<bool>> Images = new();

    internal static bool Supports(ApplicationAnalysisContext app)
        => app.InstructionSet is NewArmV8InstructionSet && app.Binary.PointerSizeBytes == 8
            && Images.GetValue(app, owner => new Lazy<bool>(() =>
            {
                using var sha = SHA256.Create();
                var hash = sha.ComputeHash(owner.Binary.GetRawBinaryContent().ToArray());
                return string.Concat(hash.Select(b => b.ToString("x2"))) == ImageHash;
            })).Value;

    public static bool Run(MethodAnalysisContext method)
    {
        var calls = method.ControlFlowGraph!.Instructions.Where(i => i is
            { OpCode: OpCode.Call, Operands: [Immediate { UnsignedValue: CheckedUnboxAddress }, ..] }).ToArray();
        if (calls.Length == 0 || !Supports(method.AppContext)) return false;
        var changed = false;
        foreach (var call in calls) changed |= Rewrite(call);
        return changed;
    }

    // Shape/type logic is independently testable, but production enters only
    // after validating the complete original image above.
    internal static bool Rewrite(Instruction call)
    {
        if (call is not { OpCode: OpCode.Call, Operands: [_, LocalVariable result, var value, var handle, ..] })
            return false;
        var type = handle switch
        {
            RuntimeClassTypeAnalysisContext klass => klass.RepresentedType,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext klass } => klass.RepresentedType,
            TypeAnalysisContext target and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext) => target,
            _ => null
        };
        if (type == null || !type.IsValueType || type.HasAnyGenericParameters()
            || type is not GenericInstanceTypeAnalysisContext && type.GenericParameters.Count > 0
            || type is GenericInstanceTypeAnalysisContext { GenericType.FullName: "System.Nullable`1" }
            || result.Type != null && (result.Type is not ByRefTypeAnalysisContext byref
                || byref.ElementType.FullName != type.FullName)
            || value is LocalVariable { Type.IsValueType: true }) return false;
        call.OpCode = OpCode.Unbox;
        call.SetOperands(result, type, value);
        result.Type = new UnboxedReference(type);
        return true;
    }
}
