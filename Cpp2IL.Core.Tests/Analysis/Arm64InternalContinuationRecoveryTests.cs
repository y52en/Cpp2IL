using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64InternalContinuationRecoveryTests
{
    private const ulong Caller = 0xEC5FFC, Thunk = 0xEC9020, Target = 0xEC6008;
    private static uint Branch(ulong from, ulong to) => 0x14000000u | (uint)(((long)to - (long)from) / 4 & 0x03FFFFFF);

    [TestCase("valid", true)]
    [TestCase("different-same-register-load", true)]
    [TestCase("internal-direct-branch", false)]
    [TestCase("registered-thunk", false)]
    [TestCase("registered-target", false)]
    [TestCase("target-not-in-method", false)]
    [TestCase("truncated", false)]
    [TestCase("missing", false)]
    [TestCase("branch-link", false)]
    [TestCase("conditional", false)]
    [TestCase("store", false)]
    [TestCase("word-load", false)]
    [TestCase("different-base", false)]
    [TestCase("zero-register", false)]
    [TestCase("writeback", false)]
    [TestCase("indirect-target", false)]
    [TestCase("nested-thunk", false)]
    public void OnlyExactNonCallingLoadAndInternalJumpCanBeExpanded(string shape, bool expected)
    {
        var raw = Convert.FromHexString("4AC547F9F9F3FF17");
        var instruction = BitConverter.GetBytes(Branch(Caller, Thunk));
        var entries = new HashSet<ulong>(); var internalAddresses = new HashSet<ulong> { Caller, Target };
        if (shape == "different-same-register-load") BitConverter.GetBytes(0xF9400063u).CopyTo(raw, 0); // ldr x3,[x3]
        if (shape == "internal-direct-branch") internalAddresses.Add(Thunk);
        if (shape == "registered-thunk") entries.Add(Thunk);
        if (shape == "registered-target") entries.Add(Target);
        if (shape == "target-not-in-method") internalAddresses.Remove(Target);
        if (shape == "branch-link") instruction[3] = 0x94;
        if (shape == "conditional") instruction = BitConverter.GetBytes(0x54000000u);
        if (shape == "store") raw[3] = 0xF9; // clear LDR bit22 rather than width
        if (shape == "store") raw[2] = (byte)(raw[2] & ~0x40);
        if (shape == "word-load") raw[3] = 0xB9;
        if (shape == "different-base") raw[0] ^= 0x20;
        if (shape == "zero-register") BitConverter.GetBytes(0xF94003FFu).CopyTo(raw, 0);
        if (shape == "writeback") BitConverter.GetBytes(0xF8408D4Au).CopyTo(raw, 0);
        if (shape == "indirect-target") BitConverter.GetBytes(0xD61F0140u).CopyTo(raw, 4);
        if (shape == "nested-thunk") BitConverter.GetBytes(Branch(Thunk+4, Thunk+100)).CopyTo(raw, 4);
        var branch = Disassembler.Disassemble(instruction, Caller, new(true,true,false)).Single();
        var calls = 0;
        var result = Arm64InternalContinuationRecovery.Match(branch, internalAddresses, address =>
        {
            calls++; Assert.That(address, Is.EqualTo(Thunk));
            return shape == "truncated" ? raw[..4] : shape == "missing" ? null : raw;
        }, entries.Contains);
        Assert.That(result != null, Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(result!.Count, Is.EqualTo(2));
            Assert.That(result[0].Mnemonic, Is.EqualTo(Arm64Mnemonic.LDR));
            Assert.That(result[1].Mnemonic, Is.EqualTo(Arm64Mnemonic.B));
            Assert.That(result[1].BranchTarget, Is.EqualTo(Target));
            Assert.That(result[0].Address, Is.EqualTo(Thunk));
        }
        if (shape is "internal-direct-branch" or "registered-thunk" or "branch-link" or "conditional")
            Assert.That(calls, Is.Zero);
    }
}
