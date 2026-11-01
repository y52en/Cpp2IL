using System;
using System.Globalization;
using System.Collections.Generic;
using System.Security.Cryptography;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recover native effects, not an invented constructor/type alias. The full
// inspected body is STP S0,S1,[X0]; STR S2,[X0,#8]; RET. It changes neither
// argument registers nor flags. Application writes around the call stay intact.
public static class NativeScalarStoreRecovery
{
    public static bool MatchesReceiverOverwriteBodies(ReadOnlySpan<byte> caller, ReadOnlySpan<byte> getter)
    {
        if (caller.Length != 56 || getter.Length != 16) return false;
        using var sha = SHA256.Create();
        string Hash(ReadOnlySpan<byte> value) => string.Concat(sha.ComputeHash(value.ToArray()).Select(b => b.ToString("x2")));
        return Hash(caller) == "4bc67eb46897947e99a08b0bef6a3ba24890243f83401e89dea92ac96c86699b"
            && Hash(getter) == "2e5e1b3f454d8ef320437b76749f1b4c097e2abce7b08a78a9b4bcd0f6b7a710";
    }

    public static bool MatchesBody(ReadOnlySpan<byte> bytes) => bytes.SequenceEqual(
        new byte[] { 0x00, 0x04, 0x00, 0x2d, 0x02, 0x08, 0x00, 0xbd, 0xc0, 0x03, 0x5f, 0xd6 });

    public static int Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.PointerSizeBytes != 8
            || app.UnityVersion.Major != 2018 || app.UnityVersion.Minor != 4) return 0;
        var graph = method.ControlFlowGraph!;
        var serial = graph.Instructions.Select(i => i.Index).DefaultIfEmpty(0).Max() + 1;
        var count = 0;
        bool? overwrittenProof = null;
        bool KillsReceiver(Instruction instruction)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate { Value: 0xaae400 }) return false;
            if (overwrittenProof is null)
            {
                try
                {
                    var bytes = app.Binary.GetRawBinaryContent();
                    var caller = checked((int)app.Binary.MapVirtualAddressToRaw(0xaae400));
                    var getter = checked((int)app.Binary.MapVirtualAddressToRaw(0xab72c8));
                    overwrittenProof = caller >= 0 && caller <= bytes.Length - 56 && getter >= 0 && getter <= bytes.Length - 16
                        && MatchesReceiverOverwriteBodies(bytes.Slice(caller, 56), bytes.Slice(getter, 16));
                }
                catch (Exception) { overwrittenProof = false; }
            }
            return overwrittenProof.Value;
        }
        foreach (var block in graph.Blocks.ToArray())
        {
            if (block.Instructions.LastOrDefault() is not { IsCall: true } call
                || call.Operands[0] is not Immediate address
                || app.MethodsByAddress.ContainsKey(address.UnsignedValue)) continue;
            bool matched;
            try
            {
                var raw = app.Binary.GetRawBinaryContent();
                var offset = checked((int)app.Binary.MapVirtualAddressToRaw(address.UnsignedValue));
                matched = offset >= 0 && offset <= raw.Length - 12 && MatchesBody(raw.Slice(offset, 12));
            }
            catch (Exception) { continue; }
            if (matched && TryRecover(graph, block, ref serial, KillsReceiver)) count++;
        }
        return count;
    }

    // The caller contract is separate from native-body verification for tests.
    public static bool TryRecover(ISILControlFlowGraph graph, Block block, ref int serial, Func<Instruction, bool>? killsReceiver = null)
    {
        if (block.Successors.Count != 1 || block.Successors[0] == graph.ExitBlock
            || block.Instructions.LastOrDefault() is not { IsCall: true } call
            || call.Operands[0] is not Immediate) return false;
        var first = call.OpCode == OpCode.Call ? 2 : 1;
        if (call.Operands.Count != first + 16
            || (first == 2 && call.Destination is not Register { Name: "X0", Version: -1 })) return false;
        for (var i = 0; i < 16; i++)
            if (call.Operands[first + i] is not Register { Version: -1 } arg
                || arg.Name != (i < 8 ? "X" + i : "V" + (i - 8))) return false;
        var receiver = Definition(block, "X0");
        if (receiver is not { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: Register slot }] }
            || slot.Version != -1 || !SlotOffset(slot, out var offset) || offset > -12 || offset % 4 != 0) return false;
        // Address aliases cannot be faithfully represented by three unrelated
        // scalar locals. Do not let the receiver escape before/after this call.
        if (block.Instructions.Skip(block.Instructions.IndexOf(receiver) + 1).TakeWhile(i => i != call)
            .Any(i => i.Sources.Any(o => UsesX0(o))) || !ReceiverDiesCore(block, killsReceiver)) return false;
        // Float literals carry proven S-register precision. Zero's bit pattern
        // is identical in S/D/integer lanes. Other values need a native-width
        // and bit-reinterpretation proof, not an inferred C# numeric conversion.
        var values = new IOperand[3];
        for (var lane = 0; lane < 3; lane++)
        {
            var definition = Definition(block, "V" + lane);
            if (definition is not { OpCode: OpCode.Move, Operands: [_, var value] }) return false;
            if (value is FloatLiteral literal) values[lane] = literal;
            else if (value is Immediate { Value: 0 }) values[lane] = new FloatLiteral(0);
            else return false;
        }
        var zeroStores = new List<(Block Block, Instruction Store, int Offset, int Width)>();
        // Independent scalar slots are valid only when all observable existing
        // uses agree with four-byte floating reads. Reject escaping addresses,
        // integer reinterpretations, wide overlapping loads and later stores.
        foreach (var instruction in graph.Instructions)
        foreach (var operand in instruction.Operands)
        {
            if (ReferenceEquals(instruction, receiver) && operand is AddressOf) continue;
            if (operand is Register overlap && SlotOffset(overlap, out var overlapOffset))
            {
                var width = Equals(operand, instruction.Destination) ? instruction.NativeWriteSize : instruction.NativeReadSize;
                if (width > 0 && overlapOffset < offset + 12 && (long)overlapOffset + width > offset
                    && (overlapOffset < offset || (long)overlapOffset + width > offset + 12)) return false;
            }
            if (!Touches(operand, offset)) continue;
            if (instruction is { OpCode: OpCode.Move, Operands: [Register written, Immediate { Value: 0 }], NativeWriteSize: 4 or 8 }
                && Equals(operand, written) && SlotOffset(written, out var zeroOffset)
                && (zeroOffset - offset) % 4 == 0 && zeroOffset + instruction.NativeWriteSize <= offset + 12)
            {
                zeroStores.Add((graph.Blocks.Single(b => b.Instructions.Contains(instruction)), instruction, zeroOffset, instruction.NativeWriteSize));
                continue;
            }
            if (operand is not Register read || !SlotOffset(read, out var readOffset)
                || (readOffset - offset) % 4 != 0
                || instruction is not { OpCode: OpCode.Move, Operands: [Register destination, _], NativeReadSize: 4 }
                || !destination.Name.StartsWith("V", StringComparison.Ordinal)
                || !Equals(operand, instruction.Operands[1])) return false;
        }
        // Compiler zero-initialization may use an eight-byte integer zero store
        // for two Single lanes. Preserve those bits as two independent zero
        // scalar definitions, only after rejecting every wider/escaping use.
        foreach (var (owner, store, start, width) in zeroStores)
        {
            var at = owner.Instructions.IndexOf(store);
            owner.Instructions.RemoveAt(at);
            for (var lane = 0; lane < width / 4; lane++)
                owner.Instructions.Insert(at + lane, new Instruction(serial++, OpCode.Move,
                    new Register(null, "stack_-" + (-(start + lane * 4)).ToString("X")), new FloatLiteral(0)) { NativeWriteSize = 4 });
        }
        block.Instructions.RemoveAt(block.Instructions.Count - 1);
        for (var lane = 0; lane < 3; lane++)
            block.Instructions.Add(new Instruction(serial++, OpCode.Move,
                new Register(null, "stack_-" + (-(offset + lane * 4)).ToString("X")), values[lane]) { NativeWriteSize = 4 });
        block.CalculateBlockType();
        return true;
    }

    private static Instruction? Definition(Block block, string name)
    {
        for (var i = block.Instructions.Count - 2; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.IsCall) return null;
            if (instruction.Destination is Register { Version: -1 } register && register.Name == name)
                return instruction;
            if (instruction.ImplicitDefinition is Register implicitRegister && implicitRegister.Name == name) return null;
        }
        return null;
    }

    private static bool SlotOffset(Register slot, out int offset)
    {
        offset = 0;
        if (!slot.Name.StartsWith("stack_-", StringComparison.Ordinal)
            || !int.TryParse(slot.Name.Substring(7), NumberStyles.AllowHexSpecifier,
                CultureInfo.InvariantCulture, out var magnitude) || magnitude <= 0) return false;
        offset = -magnitude;
        return true;
    }

    private static bool Touches(IOperand operand, int start) => operand switch
    {
        Register register => SlotOffset(register, out var offset) && offset >= start && offset < start + 12,
        AddressOf address => Touches(address.Target, start),
        MemoryOperand memory => (memory.Base != null && Touches(memory.Base, start))
            || (memory.Index != null && Touches(memory.Index, start)),
        _ => false,
    };

    private static bool UsesX0(IOperand operand) => operand switch
    {
        Register { Name: "X0" } => true,
        AddressOf address => UsesX0(address.Target),
        MemoryOperand memory => (memory.Base != null && UsesX0(memory.Base))
            || (memory.Index != null && UsesX0(memory.Index)),
        _ => false,
    };

    private static bool ReceiverDies(Block callBlock) => ReceiverDiesCore(callBlock, null);

    private static bool ReceiverDiesCore(Block callBlock, Func<Instruction, bool>? killsReceiver)
    {
        var pending = new Stack<Block>(callBlock.Successors);
        var seen = new HashSet<Block>();
        while (pending.Count > 0)
        {
            var block = pending.Pop();
            if (!seen.Add(block)) continue;
            if (seen.Count > 64 || block == callBlock) return false;
            var killed = false;
            foreach (var instruction in block.Instructions)
            {
                // The inspected no-input builder overwrites X0 from a global
                // getter before it can read/pass the incoming receiver. Keep
                // its call and every effect; only correct raw-ABI liveness.
                if (killsReceiver?.Invoke(instruction) == true) { killed = true; break; }
                if (instruction.Sources.Any(UsesX0)) return false;
                if (instruction.Destination is Register { Name: "X0" }
                    || instruction.ImplicitDefinition is Register { Name: "X0" }) { killed = true; break; }
            }
            if (!killed) foreach (var next in block.Successors) pending.Push(next);
        }
        return true;
    }
}
