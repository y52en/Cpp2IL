using System;
using System.Collections.Generic;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class FloatingCompareFlagsTests
{
    // Execute the actual IR emitted by the lifter, including overwritten temporaries.
    private static string Evaluate(double left, double right)
    {
        var a = new Register(null, "A");
        var b = new Register(null, "B");
        var values = new Dictionary<Register, double> { [a] = left, [b] = right };
        double Read(IOperand operand) => operand switch
        {
            Register r => values[r],
            FloatLiteral f => f.Value,
            DoubleLiteral d => d.Value,
            _ => throw new InvalidOperationException($"Unexpected comparison operand {operand}"),
        };
        foreach (var instruction in NewArmV8InstructionSet.FloatingCompareFlags(a, b, true))
        {
            var x = Read(instruction.Operands[1]);
            var y = instruction.Operands.Count > 2 ? Read(instruction.Operands[2]) : 0;
            values[(Register)instruction.Operands[0]] = instruction.OpCode switch
            {
                OpCode.CheckLess => x < y ? 1 : 0,
                OpCode.CheckEqual => x == y ? 1 : 0,
                OpCode.CheckGreater => x > y ? 1 : 0,
                OpCode.Not => x == 0 ? 1 : 0,
                OpCode.Or => (int)x | (int)y,
                _ => throw new InvalidOperationException($"Unexpected FP flag opcode {instruction.OpCode}"),
            };
        }
        return $"{values[new Register(null, "N")]}{values[new Register(null, "Z")]}{values[new Register(null, "C")]}{values[new Register(null, "V")]}";
    }

    [TestCase(1d, 2d, "1000")]
    [TestCase(2d, 2d, "0110")]
    [TestCase(3d, 2d, "0010")]
    [TestCase(double.NaN, 2d, "0011")]
    [TestCase(2d, double.NaN, "0011")]
    [TestCase(double.NaN, double.NaN, "0011")]
    [TestCase(double.PositiveInfinity, double.PositiveInfinity, "0110")]
    [TestCase(double.NegativeInfinity, double.PositiveInfinity, "1000")]
    [TestCase(double.PositiveInfinity, 0d, "0010")]
    [TestCase(0d, -0d, "0110")]
    public void EmittedFlagsMatchArmNzcv(double left, double right, string flags)
        => Assert.That(Evaluate(left, right), Is.EqualTo(flags));

    [TestCase(false)]
    [TestCase(true)]
    public void ImmediateZeroHasNativeFloatingWidth(bool doublePrecision)
    {
        var ir = NewArmV8InstructionSet.FloatingCompareFlags(new Register(null, "V0"), new Immediate(0), doublePrecision);
        Assert.That(ir[0].Operands[2], doublePrecision ? Is.TypeOf<DoubleLiteral>() : Is.TypeOf<FloatLiteral>());
        Assert.That(ir.Exists(i => i.OpCode is OpCode.Xor or OpCode.Subtract), Is.False);
    }
}
