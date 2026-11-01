using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Folds operations whose operands have become constant, and applies algebraic identities.
public static class ConstantFolder
{
    public static bool Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static bool Run(ISILControlFlowGraph cfg)
    {
        var changed = false;

        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        foreach (var instruction in cfg.Instructions)
            changed |= TryFoldTypedZeroDifference(instruction, cfg, definitions);
        foreach (var instruction in cfg.Instructions)
            changed |= TryFoldZeroDifference(instruction, definitions);
        foreach (var instruction in cfg.Instructions)
            changed |= TryFold(instruction);

        return changed;
    }

    private static bool TryFoldTypedZeroDifference(Instruction instruction,ISILControlFlowGraph cfg,
        System.Collections.Generic.IReadOnlyDictionary<LocalVariable,Instruction> definitions)
    {
        if(instruction is not {OpCode:OpCode.CheckEqual or OpCode.CheckNotEqual,NativeFloatingPointSize:0,
                Operands:[var destination,LocalVariable difference,Immediate {Value:0}]}
            || !definitions.TryGetValue(difference,out var subtract)
            || subtract is not {OpCode:OpCode.Subtract,NativeArithmeticSize:4,NativeFloatingPointSize:0,
                Operands:[_,LocalVariable source,Immediate {Value:0}]})return false;
        var type=source.Type;
        if(type?.IsEnumType==true)type=type.EnumUnderlyingType;
        if(type?.FullName is not ("System.Boolean" or "System.Byte" or "System.SByte" or "System.Char"
            or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32"))return false;
        // Only an unchanged local snapshot inside one straight-line block.
        // In particular, an I8 whose low W bits are zero is NOT itself zero.
        var block=cfg.Blocks.SingleOrDefault(b=>b.Instructions.Contains(subtract) && b.Instructions.Contains(instruction));
        if(block==null)return false;
        var start=block.Instructions.IndexOf(subtract);var end=block.Instructions.IndexOf(instruction);
        if(start>=end || block.Instructions.Skip(start+1).Take(end-start-1).Any(i=>ReferenceEquals(i.Destination,source))
            || cfg.Instructions.Any(i=>i.Operands.Any(o=>o is AddressOf address
                && ForwardNullCheckRecovery.Uses(address.Target,source))))return false;
        instruction.SetOperands(destination,source,new Immediate(0));return true;
    }

    private static bool TryFoldZeroDifference(Instruction instruction,
        System.Collections.Generic.IReadOnlyDictionary<LocalVariable, Instruction> definitions)
    {
        if (instruction.NativeFloatingPointSize != 0
            || instruction is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                Operands: [_, LocalVariable difference, Immediate { Value: 0 }] }
            || !definitions.TryGetValue(difference, out var definition)
            || definition is not { OpCode: OpCode.Subtract, NativeFloatingPointSize: 0,
                Operands: [_, Immediate left, Immediate right] }) return false;
        // (a-b) mod 2^N == 0 iff a == b mod 2^N. Require the SAME
        // answer at every supported machine integer width; do not assume
        // 64-bit arithmetic or silently discard W-register wraparound.
        var equal = left.Value == right.Value;
        if ((unchecked((byte)left.Value) == unchecked((byte)right.Value)) != equal
            || (unchecked((ushort)left.Value) == unchecked((ushort)right.Value)) != equal
            || (unchecked((uint)left.Value) == unchecked((uint)right.Value)) != equal) return false;
        return ToConstant(instruction, (instruction.OpCode == OpCode.CheckEqual) == equal ? 1 : 0);
    }

    private static bool TryFold(Instruction instruction)
    {
        // These operands are IEEE payloads. Integer negation/identities are
        // not float algebra (notably signed zero, NaNs and subnormal bit 1).
        if(instruction.NativeFloatingPointSize!=0)return false;
        // Unary constant folds.
        if (instruction is { OpCode: OpCode.Not, Operands: [_, Immediate n] })
            return ToConstant(instruction, instruction.Destination is LocalVariable { Type.FullName: "System.Boolean" }
                ? (n.Value == 0 ? 1 : 0) : ~n.Value);
        if (instruction is { OpCode: OpCode.Negate, Operands: [_, Immediate m] })
            return ToConstant(instruction,instruction.NativeArithmeticSize==4?unchecked((uint)-m.Value):unchecked(-m.Value));

        // metadata handles are by definition never null
        if (instruction is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, TypeAnalysisContext, var against] }
            && Constant(against) == 0)
            return ToConstant(instruction, instruction.OpCode == OpCode.CheckEqual ? 0 : 1);

        // Binary constant folds.
        if (BinaryConstants(instruction, out var a, out var b))
        {
            switch (instruction.OpCode)
            {
                case OpCode.CheckEqual: return ToConstant(instruction, a == b ? 1 : 0);
                case OpCode.CheckNotEqual: return ToConstant(instruction, a != b ? 1 : 0);
                case OpCode.And: return ToConstant(instruction, a & b);
                case OpCode.Or: return ToConstant(instruction, a | b);
                case OpCode.Xor: return ToConstant(instruction, a ^ b);
                case OpCode.ShiftLeft: return ToConstant(instruction, a << (int)(b & 0x3F));
                case OpCode.ShiftRight: return ToConstant(instruction, a >> (int)(b & 0x3F));
                case OpCode.ShiftRightUnsigned:
                    if(instruction.NativeArithmeticSize==4)return ToConstant(instruction,(uint)a>>(int)(b&31));
                    if(instruction.NativeArithmeticSize==8)return ToConstant(instruction,unchecked((long)((ulong)a>>(int)(b&63))));
                    return false; // Unknown native width is not a 64-bit proof.
            }
        }

        // One-constant algebraic identities.
        // A native word operation may truncate/extend even when its arithmetic
        // looks like an identity. A plain Move would discard that contract.
        if(instruction.NativeArithmeticSize==4 && instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
            || instruction.OpCode==OpCode.Multiply && instruction.NativeArithmeticSize==8 && instruction.NativeMultiplyInputSize==4)
            return false;
        switch (instruction.OpCode)
        {
            case OpCode.And:
                if (Constant(instruction.Operands[1]) == 0 || Constant(instruction.Operands[2]) == 0)
                    return ToConstant(instruction, 0);
                // x & 1 == x only when x is a 0/1 boolean
                return BooleanIdentity(instruction, 1) is { } andBool && ToMove(instruction, andBool);
            case OpCode.Or:
            case OpCode.Xor:
            case OpCode.Add:
                return Identity(instruction, 0);
            case OpCode.Multiply:
                return Identity(instruction, 1);
            case OpCode.Subtract:
            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:
            case OpCode.ShiftRightUnsigned:
                // right identity only: x - 0 / x << 0 / x >> 0 == x, but 0 - x etc. are not
                return Constant(instruction.Operands[2]) == 0 && ToMove(instruction, instruction.Operands[1]);
        }

        return false;
    }

    // For a commutative op, if one operand is the identity constant, the result is the other operand.
    private static bool Identity(Instruction instruction, long identity)
    {
        if (Constant(instruction.Operands[1]) == identity)
            return ToMove(instruction, instruction.Operands[2]);
        if (Constant(instruction.Operands[2]) == identity)
            return ToMove(instruction, instruction.Operands[1]);
        return false;
    }

    // The boolean operand of `bool & const`, or null if that isn't the shape.
    private static IOperand? BooleanIdentity(Instruction instruction, long constant)
    {
        if (Constant(instruction.Operands[2]) == constant && IsBoolean(instruction.Operands[1]))
            return instruction.Operands[1];
        if (Constant(instruction.Operands[1]) == constant && IsBoolean(instruction.Operands[2]))
            return instruction.Operands[2];
        return null;
    }

    private static bool IsBoolean(IOperand operand) => operand is LocalVariable { Type.FullName: "System.Boolean" };

    private static bool BinaryConstants(Instruction instruction, out long left, out long right)
    {
        (left, right) = (0, 0);

        if (instruction.Operands is [_, Immediate a, Immediate b])
        {
            (left, right) = (a.Value, b.Value);
            return true;
        }

        return false;
    }

    private static long? Constant(IOperand operand) => operand is Immediate immediate ? immediate.Value : null;

    private static bool ToConstant(Instruction instruction, long value)
    {
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(instruction.Operands[0], new Immediate(value));
        return true;
    }

    private static bool ToMove(Instruction instruction, IOperand source)
    {
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(instruction.Operands[0], source);
        return true;
    }
}
