using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

public static class NativeNumericConversion
{
    public static (TypeAnalysisContext Target, TypeAnalysisContext Source)? Contract(
        SystemTypesContext types, Arm64Mnemonic mnemonic, Arm64Register destination, Arm64Register source)
    {
        TypeAnalysisContext? Float(Arm64Register register) => register switch
        {
            >= Arm64Register.S0 and <= Arm64Register.S31 => types.SystemSingleType,
            >= Arm64Register.D0 and <= Arm64Register.D31 => types.SystemDoubleType,
            _ => null
        };
        TypeAnalysisContext? Integer(Arm64Register register, bool unsigned) => register switch
        {
            >= Arm64Register.W0 and <= Arm64Register.W30 => unsigned ? types.SystemUInt32Type : types.SystemInt32Type,
            >= Arm64Register.X0 and <= Arm64Register.X30 => unsigned ? types.SystemUInt64Type : types.SystemInt64Type,
            // Scalar SIMD integer payloads also have exact native widths.
            // SCVTF S0,S0 converts integer bits loaded into S0, not a float copy.
            >= Arm64Register.S0 and <= Arm64Register.S31 => unsigned ? types.SystemUInt32Type : types.SystemInt32Type,
            >= Arm64Register.D0 and <= Arm64Register.D31 => unsigned ? types.SystemUInt64Type : types.SystemInt64Type,
            _ => null
        };
        var pair = mnemonic switch
        {
            Arm64Mnemonic.FCVTZS => (Integer(destination, false), Float(source)),
            Arm64Mnemonic.FCVTZU => (Integer(destination, true), Float(source)),
            Arm64Mnemonic.SCVTF => (Float(destination), Integer(source, false)),
            Arm64Mnemonic.UCVTF => (Float(destination), Integer(source, true)),
            Arm64Mnemonic.FCVT => (Float(destination), Float(source)),
            _ => (null, null)
        };
        if (pair.Item1 == null || pair.Item2 == null
            || mnemonic == Arm64Mnemonic.FCVT && ReferenceEquals(pair.Item1, pair.Item2)) return null;
        return (pair.Item1, pair.Item2);
    }
}
