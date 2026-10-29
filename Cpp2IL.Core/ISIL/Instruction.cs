using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class Instruction : IOperand
{
    public int Index;

    public OpCode OpCode
    {
        get;
        set
        {
            if (field == value)
                return;

            field = value;
            _arm64IndirectArgumentSnapshot = null;
            ResetSources();
        }
    }

    private List<IOperand> _operands;

    // Ordered physical argument slots are established ONLY on a raw ARM64
    // BR/BLR snapshot. SSA may substitute a value from another register into
    // an existing slot; that does not change the slot's physical position.
    // Keep a storage witness too: externally aliased constructor lists cannot
    // silently reorder a previously certified snapshot.
    private IOperand[]? _arm64IndirectArgumentSnapshot;

    internal bool HasArm64IndirectArgumentSnapshot
    {
        get
        {
            if (OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump)
                || _arm64IndirectArgumentSnapshot is not { Length: 18 } witness
                || _operands.Count != 18) return false;
            for (var i = 0; i < 18; i++)
                if (!ReferenceEquals(_operands[i], witness[i])) return false;
            return true;
        }
    }

    internal bool MarkArm64IndirectArgumentSnapshot()
    {
        _arm64IndirectArgumentSnapshot = null;
        if (OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump) || _operands.Count != 18)
            return false;
        for (var i = 0; i < 16; i++)
            if (_operands[2 + i] is not Register r
                || r.Name != (i < 8 ? "X" + i : "V" + (i - 8))) return false;
        _arm64IndirectArgumentSnapshot = _operands.ToArray();
        return true;
    }

    public OperandList Operands => new(_operands);

    // Exists to clear the return register after a CallVoid, basically.
    public Register? ImplicitDefinition;
    // Proven byte width of a lifted native store; zero means unknown.
    public int NativeWriteSize;
    // Proven native memory read width; destination register size can differ (LDRSW).
    public int NativeReadSize;
    // Proven width of a lifted integer arithmetic/shift result, not an inferred pointer/type.
    public int NativeArithmeticSize;
    // Original multiply input width/sign, retained without hiding affine
    // address expressions behind scalar casts before array/field recovery.
    public int NativeMultiplyInputSize;
    public bool NativeMultiplySigned;
    // Width of an unmodified native register/address copy; extensions are not copies.
    public int NativeRegisterCopySize;
    // Scalar floating result width proven by S/D operands, not inferred from a
    // reused V register or from the eventual managed destination type.
    public int NativeFloatingPointSize;
    // Signedness is part of the comparison, not inferred from a C# type name.
    public bool UnsignedComparison;
    // Proven native INTEGER comparison operand width; not the boolean result
    // width or an inferred managed signedness. Zero means unknown.
    public int NativeComparisonSize;
    // Integer extension reads a low-bit VIEW of a GPR. Its conversion source
    // type must not retag the entire producer local (which may have X users).
    public bool NativeIntegerSourceView;
    // Width proven zero by native initialization or contiguous effect-free stack zero stores (not a scalar guess).
    public int NativeZeroSize;
    // Proven vtable/interface dispatch, distinct from a direct call to a virtual
    // method (e.g. base.Method). Preserve that distinction in managed IL.
    public bool NativeVirtualDispatch;
    // A separately proven native null guard is carried by CIL callvirt on a
    // NONvirtual method. This does not claim vtable or interface dispatch.
    public bool NativeNullCheckedCall;
    // Original direct native entry, captured before metadata replaces the raw
    // call operand. Not inferred from a generic definition's boxed wrapper.
    public ulong NativeDirectCallTarget;
    // Exact pre-SSA result-storage extent, proved by unanimous native ABI or
    // the call's own reaching MethodInfo and registered native entry.
    public int NativeReturnStorageSize;

    public bool IsFallThrough =>
        OpCode switch
        {
            OpCode.Return or OpCode.Jump or OpCode.ConditionalJump or OpCode.IndirectJump or OpCode.Throw => false,
            _ => true
        };

    public bool IsCall => OpCode is OpCode.Call or OpCode.CallVoid;

    public bool IsAssignment => Destination != null;

    public OperandList Sources => new(_sources.Value);
    private Lazy<List<IOperand>> _sources;

    public OperandList SourcesAndConstants => new(_sourcesAndConstants.Value);
    private Lazy<List<IOperand>> _sourcesAndConstants;

    public Instruction(int index, OpCode opcode, params List<IOperand> operands)
    {
        Index = index;
        OpCode = opcode;
        _operands = operands;
        ResetSources();
    }

    [MemberNotNull(nameof(_operands))]
    public void SetOperands(params List<IOperand> operands)
    {
        _arm64IndirectArgumentSnapshot = null;
        _operands = operands;
        ResetSources();
    }

    public void SetOperand(int index, IOperand value)
    {
        var preserveSnapshot = HasArm64IndirectArgumentSnapshot;
        _operands[index] = value;
        if (preserveSnapshot) _arm64IndirectArgumentSnapshot![index] = value;
        else _arm64IndirectArgumentSnapshot = null;
        ResetSources();
    }

    public void AddOperands(IEnumerable<IOperand> operands)
    {
        _arm64IndirectArgumentSnapshot = null;
        _operands.AddRange(operands);
        ResetSources();
    }

    public void RemoveOperandAt(int index)
    {
        _arm64IndirectArgumentSnapshot = null;
        _operands.RemoveAt(index);
        ResetSources();
    }

    public IOperand? Destination
    {
        get => GetOrSetDestination();
        set => GetOrSetDestination(value);
    }

    private IOperand? GetOrSetDestination(IOperand? newDestination = null)
    {
        switch (OpCode)
        {
            case OpCode.Move:
            case OpCode.Phi:
            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:
            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:
            case OpCode.ShiftRightUnsigned:
            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
            case OpCode.Not:
            case OpCode.Negate:
            case OpCode.Absolute:
            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:
            case OpCode.Newobj:
            case OpCode.NewArr:
            case OpCode.Box:
            case OpCode.IsInst:
            case OpCode.CastClass:
            case OpCode.Unbox:
            case OpCode.UnboxAny:
            case OpCode.NumericConvert:
            case OpCode.LoadVirtualFunction:
            case OpCode.NewVirtualDelegate:
                if (newDestination != null)
                    SetOperand(0, newDestination);
                return IsConstantValue(_operands[0]) ? null : _operands[0];

            // A call's operand 0 is the target; its return value is operand 1 (per OpCode.Call).
            // CallVoid has no return value and so has no destination, and a Call may also be emitted
            // without a return-value operand, in which case it likewise has no destination.
            case OpCode.Call:
            case OpCode.IndirectCall:
                if (_operands.Count < 2)
                    return null;
                if (newDestination != null)
                    SetOperand(1, newDestination);
                return IsConstantValue(_operands[1]) ? null : _operands[1];

            default:
                return null;
        }
    }

    [MemberNotNull(nameof(_sources), nameof(_sourcesAndConstants))]
    private void ResetSources()
    {
        if (_sources is { IsValueCreated: false } && _sourcesAndConstants is { IsValueCreated: false })
        {
            return;
        }

        _sources = new Lazy<List<IOperand>>(() => GetSources());
        _sourcesAndConstants = new Lazy<List<IOperand>>(() => GetSources(false));
    }

    private List<IOperand> GetSources(bool constantsOnly = true)
    {
        var sources = OpCode switch
        {
            OpCode.Move or OpCode.ConditionalJump
                or OpCode.ShiftStack or OpCode.Not or OpCode.Negate or OpCode.Absolute
                or OpCode.Newobj
                => [_operands[1]],

            OpCode.Box or OpCode.IsInst or OpCode.CastClass or OpCode.Unbox or OpCode.UnboxAny => [_operands[2]],
            OpCode.ArrayNullCheck => [_operands[0]],
            OpCode.NumericConvert => [_operands[3]],
            OpCode.LoadVirtualFunction => [_operands[2]],
            OpCode.NewVirtualDelegate => [_operands[3]],

            OpCode.Add or OpCode.Subtract or OpCode.Multiply
                or OpCode.Divide or OpCode.Modulo or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.ShiftRightUnsigned
                or OpCode.And or OpCode.Or or OpCode.Xor
                => [_operands[2], _operands[1]],

            OpCode.Call => _operands.Skip(2).ToList(),

            // Unlike a direct call, operand 0 is the address being called and so is itself a source.
            OpCode.IndirectCall => _operands.Count > 2
                ? _operands.Skip(2).Prepend(_operands[0]).ToList()
                : _operands.Take(1).ToList(),

            OpCode.CallVoid or OpCode.Phi or OpCode.NewArr => _operands.Skip(1).ToList(),
            OpCode.CheckEqual or OpCode.CheckGreater or OpCode.CheckLess
                or OpCode.CheckNotEqual or OpCode.CheckGreaterOrEqual or OpCode.CheckLessOrEqual
                => [_operands[1], _operands[2]],

            _ => []
        };

        if (OpCode == OpCode.Return && _operands.Count == 1)
            sources.Add(_operands[0]);

        if (constantsOnly)
            sources = sources.Where(o => !IsConstantValue(o)).ToList();

        return sources;
    }

    public override string ToString()
    {
        if (OpCode == OpCode.Jump && _operands[0] is Immediate jumpTarget)
            return $"{Index} {OpCode} {jumpTarget.Value:X4}";
        if (OpCode == OpCode.ConditionalJump && _operands[0] is Immediate jumpTarget2)
            return $"{Index} {OpCode} {jumpTarget2.Value:X4}, {FormatOperand(_operands[1])}";

        if ((OpCode is OpCode.CallVoid or OpCode.Call) && _operands[0] is Immediate callTarget)
        {
            var remainingOperands = string.Join(", ", _operands.Skip(1).Select(FormatOperand));
            return string.IsNullOrEmpty(remainingOperands)
                ? $"{Index} {OpCode} {callTarget.Value:X4}"
                : $"{Index} {OpCode} {callTarget.Value:X4}, {remainingOperands}";
        }

        var formattedOperands = string.Join(", ", _operands.Select(FormatOperand));
        return string.IsNullOrEmpty(formattedOperands)
            ? $"{Index} {OpCode}"
            : $"{Index} {OpCode} {formattedOperands}";
    }

    private static string FormatOperand(IOperand operand)
    {
        return operand switch
        {
            MethodAnalysisContext method => $"{method.DeclaringType!.Name}.{method.Name}",
            RuntimeMethodInfoAnalysisContext methodInfo => $"methodof({methodInfo.RepresentedMethod.FullName})",
            RuntimeFieldInfoAnalysisContext fieldInfo => $"fieldof({fieldInfo.RepresentedField.DeclaringType.FullName}.{fieldInfo.RepresentedField.Name})",
            TypeAnalysisContext type => $"typeof({type.FullName})",
            Instruction instruction => $"@{instruction.Index}",
            Block block => $"@b{block.ID}",
            _ => operand.ToString()!
        };
    }

    public static bool IsConstantValue(IOperand operand) =>
        operand switch
        {
            Register or StackOffset or LocalVariable => false,
            AddressOf or ArrayAccess or ArrayLength => false,
            MemoryOperand memory => memory.IsConstant,
            _ => true
        };

    // Deliberately not Equals/GetHashCode. Instructions are identity objects: the graph, stack analyzer and
    // IL generator all key sets and dictionaries on the specific instruction instance, and generated
    // instructions (phi copies, for one) are routinely structurally identical to each other.
    public bool IsStructurallyEqualTo(Instruction? other)
    {
        if (ReferenceEquals(this, other))
            return true;

        if (other is null)
            return false;

        if (OpCode != other.OpCode)
            return false;

        if (Index != other.Index)
            return false;

        if (_operands.Count != other._operands.Count)
            return false;

        for (var i = 0; i < _operands.Count; i++)
        {
            var thisOperand = _operands[i];
            var otherOperand = other._operands[i];

            // Branch targets are compared by index, so a back edge doesn't send us round in circles.
            if (thisOperand is Instruction thisTarget)
            {
                if (otherOperand is not Instruction otherTarget || thisTarget.Index != otherTarget.Index)
                    return false;

                continue;
            }

            if (!thisOperand.Equals(otherOperand))
                return false;
        }

        return true;
    }
}
