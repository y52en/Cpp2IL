using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// Original Marshall EC5D50 -> EC9020: LDR X10,[X10,#0xF88]; B EC6008.
// EC6008 is ALREADY an instruction in this method, not a callable entry.
// Expand only this finite, exact unsigned 64-bit self-register load + direct
// branch shape. Keep the real load, register effects and exception behavior;
// do not infer a signature or invent a return/call ABI for a continuation.
public static class Arm64InternalContinuationRecovery
{
    public static IReadOnlyList<Arm64Instruction>? Match(Arm64Instruction branch,
        IReadOnlySet<ulong> internalAddresses, Func<ulong, byte[]?> readEight, Func<ulong, bool> registeredEntry)
    {
        if (branch.Mnemonic != Arm64Mnemonic.B
            || branch.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL)
            || internalAddresses.Contains(branch.BranchTarget) || (branch.BranchTarget & 3) != 0
            || registeredEntry(branch.BranchTarget)) return null;
        var raw = readEight(branch.BranchTarget);
        if (raw is not { Length: 8 }) return null;
        var load = BitConverter.ToUInt32(raw, 0); var jump = BitConverter.ToUInt32(raw, 4);
        // LDR Xt,[Xn,#uimm12*8], Xt == Xn, neither SP nor XZR. No writeback,
        // register-index, sign-extension, literal pool, flags, or LR mutation.
        if ((load & 0xFFC00000u) != 0xF9400000u || (jump & 0xFC000000u) != 0x14000000u
            || (load & 31) == 31 || (load & 31) != ((load >> 5) & 31)) return null;
        var delta = (long)(jump & 0x03FFFFFFu);
        if ((delta & (1L << 25)) != 0) delta -= 1L << 26;
        var target = unchecked((ulong)((long)branch.BranchTarget + 4 + delta * 4));
        if (!internalAddresses.Contains(target) || registeredEntry(target)) return null;
        try
        {
            var instructions = Disassembler.Disassemble(raw, branch.BranchTarget, new(true, true, false)).ToArray();
            return instructions is [{ Mnemonic: Arm64Mnemonic.LDR }, { Mnemonic: Arm64Mnemonic.B }]
                && instructions[1].BranchTarget == target ? instructions : null;
        }
        catch (Exception) { return null; }
    }

    public static IReadOnlyList<Arm64Instruction>? For(MethodAnalysisContext method, Arm64Instruction branch,
        IReadOnlySet<ulong> internalAddresses)
    {
        var app = method.AppContext;
        if (app.Binary.PointerSizeBytes != 8 || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return null;
        return Match(branch, internalAddresses, address =>
        {
            try
            {
                var offset = checked((int)app.Binary.MapVirtualAddressToRaw(address));
                var content = app.Binary.GetRawBinaryContent();
                if (offset < 0 || offset > content.Length - 8
                    || app.Binary.MapVirtualAddressToRaw(address + 7) != (long)offset + 7) return null;
                return content.Slice(offset, 8).ToArray();
            }
            catch (Exception) { return null; }
        }, address => app.MethodsByAddress.ContainsKey(address));
    }
}
