using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers high-level relational conditions from the explicit EFLAGS computations the lifter emits.
///
/// The x86 lifter models a <c>cmp</c>/<c>test</c> as a cluster of flag pseudo-registers
/// (ZF = (a-b)==0, SF = (a-b)&lt;0, OF = signed overflow, ...) and lowers each <c>jcc</c> into a
/// boolean expression over those flags. This pass recognises those canonical shapes for every
/// <see cref="OpCode.ConditionalJump"/> condition and rewrites the condition's defining instruction
/// into a single relational comparison (==, !=, &lt;, &lt;=, &gt;, &gt;=) on the original compare
/// operands. The now-orphaned flag arithmetic is removed by the dead-code pass that runs next.
///
/// Runs in SSA form, where each flag/temporary has a single, version-stable definition, so the
/// operands referenced at the branch are provably the ones captured at the compare.
///
/// Note: the lifter lowers the unsigned conditions (ja/jae/jb/jbe) with the same flag expressions as
/// their signed counterparts, so they are recovered as signed comparisons too - matching the
/// existing (signed) behaviour rather than introducing a new inaccuracy.
/// </summary>
public static class FlagConditionRecovery
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);
        var ambiguous=cfg.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()!=1).Select(g=>g.Key).ToHashSet();

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode != OpCode.ConditionalJump)
                    continue;

                if (instruction.Operands[1] is not LocalVariable condition)
                    continue;

                if (!TryClassify(condition, defOf, out var relop, out var op0, out var op1))
                    continue;

                // Rewrite the condition's defining instruction in place into a single comparison.
                // Its destination (the condition local the branch reads) is preserved.
                var definition = defOf[condition];
                var comparisonSize=ProveComparisonSize(condition,defOf,ambiguous,op0!,op1!);
                definition.OpCode = relop;
                definition.SetOperands(definition.Operands[0], op0!, op1!);
                definition.NativeComparisonSize=comparisonSize;
            }
        }
    }

    // Preserve the originating operation's width before flag temporaries die.
    // Do not follow input producers: an X-width comparison can consume values
    // which happened to originate in W registers, and is still 64-bit.
    internal static int ProveComparisonSize(LocalVariable condition,
        Dictionary<LocalVariable,Instruction> definitions,HashSet<LocalVariable> ambiguous,
        IOperand left,IOperand right)
    {
        var visited=new HashSet<LocalVariable>();var active=new HashSet<LocalVariable>();var widths=new HashSet<int>();
        var found=false;
        bool Same(IOperand a,IOperand b)=>ReferenceEquals(a,b)
            || a is Immediate x && b is Immediate y && x.Value==y.Value;
        bool Visit(IOperand value,int depth)
        {
            if(depth>32)return false;
            if(Same(value,left)||Same(value,right)||value is Immediate)return true;
            if(value is not LocalVariable local||ambiguous.Contains(local))return false;
            if(active.Contains(local))return false;
            if(!visited.Add(local))return true;
            active.Add(local);
            if(!definitions.TryGetValue(local,out var instruction))return false;
            if(instruction.NativeComparisonSize!=0)
            {
                if(instruction.NativeComparisonSize is not (4 or 8))return false;
                widths.Add(instruction.NativeComparisonSize);
            }
            if(instruction is {OpCode:OpCode.Subtract,Operands:[_,var a,var b]})
            {
                if(!Same(a,left)||!Same(b,right)||instruction.NativeArithmeticSize is not (4 or 8))return false;
                widths.Add(instruction.NativeArithmeticSize);found=true;active.Remove(local);return true;
            }
            if(instruction.OpCode is not (OpCode.Not or OpCode.CheckEqual or OpCode.CheckLess
                or OpCode.CheckNotEqual or OpCode.And or OpCode.Or or OpCode.Xor))return false;
            var valid=instruction.Sources.All(source=>Visit(source,depth+1));
            active.Remove(local);return valid;
        }
        return Visit(condition,0)&&found&&widths.Count==1?widths.Single():0;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    defs[destination] = instruction;

        return defs;
    }

    private static bool TryClassify(LocalVariable condition, Dictionary<LocalVariable, Instruction> defOf,
        out OpCode relop, out IOperand? op0, out IOperand? op1)
    {
        relop = default;

        // ZF on its own  =>  a == b   (je)
        if (IsZeroFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckEqual; return true; }
        // SF on its own  =>  a < b    (js; exact for the common test-against-self case)
        if (IsSignFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }

        var definition = Def(condition, defOf);
        if (definition == null)
            return false;

        switch (definition.OpCode)
        {
            case OpCode.Not:
                var inner = AsLocal(definition.Operands[1]);
                if (IsZeroFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckNotEqual; return true; }          // !ZF        => !=  (jne)
                if (IsSignFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }    // !SF        => >=  (jns)
                if (IsSignEqualsOverflow(inner, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }    // !(SF==OF)  => <   (jl/jb)
                return false;

            case OpCode.CheckEqual:
                // SF == OF  =>  a >= b   (jge/jae)
                if (IsSignFlag(AsLocal(definition.Operands[1]), defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }
                return false;

            case OpCode.And:
                // (SF==OF) && !ZF  =>  a > b   (jg/ja)
                if (IsSignGreater(definition, defOf, out op0, out op1)) { relop = OpCode.CheckGreater; return true; }
                return false;

            case OpCode.Or:
                // !(SF==OF) || ZF  =>  a <= b   (jle/jbe)
                if (IsSignLessOrEqual(definition, defOf, out op0, out op1)) { relop = OpCode.CheckLessOrEqual; return true; }
                return false;

            default:
                return false;
        }
    }

    // ZF: local := CheckEqual(t, 0) where t := Subtract(a, b)
    private static bool IsZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // SF: local := CheckLess(t, 0) where t := Subtract(a, b)
    private static bool IsSignFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckLess, UnsignedComparison: false } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Subtract(a, b)
    private static bool IsSubtraction(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.Subtract })
            return false;
        op0 = def.Operands[1];
        op1 = def.Operands[2];
        return true;
    }

    // local := CheckEqual(SF, OF) - the signed "not less" test. Operands are taken from the SF side.
    private static bool IsSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual })
            return false;
        return IsSignFlag(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Not(CheckEqual(SF, OF))
    private static bool IsNotSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.Not })
            return false;
        return IsSignEqualsOverflow(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Not(ZF)
    private static bool IsNotZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf)
    {
        var def = Def(local, defOf);
        return def is { OpCode: OpCode.Not } && IsZeroFlag(AsLocal(def.Operands[1]), defOf, out _, out _);
    }

    // And((SF==OF), !ZF), in either operand order
    private static bool IsSignGreater(Instruction and, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(and.Operands[1]);
        var right = AsLocal(and.Operands[2]);

        if (IsSignEqualsOverflow(left, defOf, out op0, out op1) && IsNotZeroFlag(right, defOf))
            return true;
        if (IsSignEqualsOverflow(right, defOf, out op0, out op1) && IsNotZeroFlag(left, defOf))
            return true;

        op0 = op1 = null;
        return false;
    }

    // Or(!(SF==OF), ZF), in either operand order
    private static bool IsSignLessOrEqual(Instruction or, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(or.Operands[1]);
        var right = AsLocal(or.Operands[2]);

        if (IsNotSignEqualsOverflow(left, defOf, out op0, out op1) && IsZeroFlag(right, defOf, out _, out _))
            return true;
        if (IsNotSignEqualsOverflow(right, defOf, out op0, out op1) && IsZeroFlag(left, defOf, out _, out _))
            return true;

        op0 = op1 = null;
        return false;
    }

    private static Instruction? Def(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf)
        => local != null && defOf.TryGetValue(local, out var def) ? def : null;

    private static LocalVariable? AsLocal(IOperand operand) => operand as LocalVariable;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
