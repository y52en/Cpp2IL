using System;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers literals which are being put into float fields/used as float constants,
/// converting them from their uint bit patterns into actual float/double literals.
/// </summary>
public static class FloatLiteralRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            // Unlike a guessed managed type, an actual scalar FADD/FSUB/etc.
            // proves that integer constants forwarded into its operands are
            // native IEEE bits, not numbers requiring conv.r4/conv.r8.
            if(instruction.NativeFloatingPointSize is 4 or 8
                && instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Negate or OpCode.Absolute)
            {
                var type=instruction.NativeFloatingPointSize==4
                    ? method.AppContext.SystemTypes.SystemSingleType : method.AppContext.SystemTypes.SystemDoubleType;
                for(var index=1;index<instruction.Operands.Count;index++)TryConvert(instruction,index,type,true);
            }
            if (instruction.OpCode == OpCode.Move && instruction.Operands is [FieldReference field, _])
                TryConvert(instruction, 1, field.Field.FieldType);
            else if (instruction.OpCode == OpCode.Move && instruction.Operands is [LocalVariable { Type: { } localType }, _])
                TryConvert(instruction, 1, localType);
            else if (instruction.IsCall && instruction.Operands is [MethodAnalysisContext target, ..])
                ConvertArguments(instruction, target);
        }
    }

    private static void ConvertArguments(Instruction call, MethodAnalysisContext target)
    {
        var firstArgument = (call.OpCode == OpCode.Call ? 2 : 1) + (target.IsStatic ? 0 : 1);

        for (var i = 0; i < target.Parameters.Count; i++)
        {
            var index = firstArgument + i;

            if (index >= call.Operands.Count)
                break;

            TryConvert(call, index, target.Parameters[i].ParameterType);
        }
    }

    private static void TryConvert(Instruction instruction, int operandIndex, TypeAnalysisContext type, bool nativeFloatingProof=false)
    {
        if (!TryGetIntegerBits(instruction.Operands[operandIndex], out var bits))
            return;

        // TODO FIXME: We have to compare by name, not reference, because a field on a generic type resolves
        // TODO FIXME: to its own Single/Double context instance rather than the canonical one in SystemTypes.
        switch (type.FullName)
        {
            case "System.Single" when nativeFloatingProof || !IsSubnormalSingle((uint)bits):
                instruction.SetOperand(operandIndex, new FloatLiteral(BitConverter.ToSingle(BitConverter.GetBytes((uint)bits), 0)));
                break;
            case "System.Double" when nativeFloatingProof || !IsSubnormalDouble(bits):
                instruction.SetOperand(operandIndex, new DoubleLiteral(BitConverter.ToDouble(BitConverter.GetBytes(bits), 0)));
                break;
        }
    }

    private static bool TryGetIntegerBits(IOperand operand, out ulong bits)
    {
        if (operand is Immediate immediate)
        {
            bits = immediate.UnsignedValue;
            return true;
        }

        bits = 0;
        return false;
    }

    // A subnormal has a zero exponent and a non-zero mantissa (zero itself is exempt). Real source
    // constants are never subnormal, so such a decode is a mislabelled integer rather than a float.
    private static bool IsSubnormalSingle(uint bits) => (bits & 0x7F800000u) == 0 && (bits & 0x007FFFFFu) != 0;

    private static bool IsSubnormalDouble(ulong bits) => (bits & 0x7FF0000000000000UL) == 0 && (bits & 0x000FFFFFFFFFFFFFUL) != 0;
}
