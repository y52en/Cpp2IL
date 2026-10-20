using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Primitive STORAGE only, never a guessed managed class/pointer/enum. Every
// write and every use must agree; unknown consumers poison the whole component.
public static class NativeScalarStorageRecovery
{
    private const int I4=1,I8=2,R4=4,R8=8,Integers=3,All=15;
    private readonly record struct Value(LocalVariable? Local,int Fixed);
    private readonly record struct Relation(Value Left,Value Right,int Allowed);
    private static int Kind(TypeAnalysisContext? type)=>type?.FullName switch
    {
        "System.Int32" or "System.UInt32"=>I4,
        "System.Int64" or "System.UInt64"=>I8,
        "System.Single"=>R4,"System.Double"=>R8,_=>0
    };

    public static int Run(MethodAnalysisContext method)
        =>method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            && method.AppContext.Binary.PointerSizeBytes==8 ? Recover(method):0;

    internal static int Recover(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not { } graph)return 0;
        var instructions=graph.Instructions.ToArray();
        var variables=instructions.Select(i=>i.Destination).OfType<LocalVariable>()
            .Where(v=>v.Type==null && !method.ParameterLocals.Contains(v)).Distinct().ToArray();
        var domains=variables.ToDictionary(v=>v,v=>v.Register.Name.StartsWith("V",StringComparison.Ordinal)?R4|R8:
            v.Register.Name.StartsWith("X",StringComparison.Ordinal) || v.Register.Name.StartsWith("W",StringComparison.Ordinal)?Integers:All);
        var relations=new List<Relation>();
        HashSet<LocalVariable> handled=[];
        Value View(IOperand operand)=>operand switch
        {
            LocalVariable v when domains.ContainsKey(v)=>new(v,0),
            LocalVariable v=>new(null,Kind(v.Type)),
            FloatLiteral=>new(null,R4),DoubleLiteral=>new(null,R8),
            Immediate {Value:0}=>new(null,All),
            Immediate {Value:>=int.MinValue and <=uint.MaxValue}=>new(null,Integers),
            Immediate=>new(null,I8),
            FieldReference f=>new(null,Kind(f.Field.FieldType)),
            ArrayAccess a when a.Array.Type is SzArrayTypeAnalysisContext t=>new(null,Kind(t.ElementType)),
            ArrayLength=>new(null,I4),_=>new(null,0)
        };
        void Pair(IOperand left,IOperand right,int allowed=All)
        {
            var a=View(left);var b=View(right);relations.Add(new(a,b,allowed));
            if(a.Local!=null)handled.Add(a.Local);if(b.Local!=null)handled.Add(b.Local);
        }
        void Require(IOperand value,int mask)
        {
            var a=View(value);relations.Add(new(a,new(null,mask),mask));
            if(a.Local!=null)handled.Add(a.Local);
        }
        foreach(var instruction in instructions)
        {
            handled=[];
            switch(instruction.OpCode)
            {
                case OpCode.Move when instruction.Operands is [var target,var source]:
                    Pair(target,source);
                    if(target is ArrayAccess stored)Require(stored.Index,Integers);
                    if(source is ArrayAccess read)Require(read.Index,Integers);
                    break;
                case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.And or OpCode.Or or OpCode.Xor
                    when instruction.Operands is [var target,var left,var right]:
                    var allowed=instruction.NativeFloatingPointSize switch {4=>R4,8=>R8,_=>
                        instruction.NativeArithmeticSize switch {4=>I4,8=>I8,_=>Integers}};
                    Pair(target,left,allowed);Pair(target,right,allowed);Pair(left,right,allowed);break;
                case OpCode.Divide when instruction.NativeFloatingPointSize is 4 or 8
                    && instruction.Operands is [var target,var left,var right]:
                    var precision=instruction.NativeFloatingPointSize==4?R4:R8;
                    Pair(target,left,precision);Pair(target,right,precision);Pair(left,right,precision);break;
                case OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess or OpCode.CheckGreater
                    or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                    when instruction.Operands is [_,var left,var right]:
                    Pair(left,right);break;
                case OpCode.NumericConvert when instruction.Operands is [var target,TypeAnalysisContext to,TypeAnalysisContext from,var source]:
                    Require(target,Kind(to));Require(source,Kind(from));break;
                case OpCode.Return when instruction.Operands.Count==1:
                    Require(instruction.Operands[0],Kind(method.ReturnType));break;
                case OpCode.NewArr when instruction.Operands.Count==3:
                    Require(instruction.Operands[2],Integers);break;
                case OpCode.Box when instruction.Operands is [_,TypeAnalysisContext type,var value]:
                    Require(value,Kind(type));break;
                case OpCode.Call or OpCode.CallVoid when instruction.Operands.Count>0
                    && instruction.Operands[0] is MethodAnalysisContext called:
                    var first=instruction.OpCode==OpCode.Call?2:1;
                    if(instruction.OpCode==OpCode.Call && instruction.Operands.Count>1)Require(instruction.Operands[1],Kind(called.ReturnType));
                    if(!called.IsStatic)first++;
                    for(var p=0;p<called.Parameters.Count && first+p<instruction.Operands.Count;p++)
                        Require(instruction.Operands[first+p],Kind(called.Parameters[p].ParameterType));
                    break;
            }
            // Complete operand traversal, not Sources (which omits field and
            // memory bases). An unresolved pointer/receiver/opaque use cannot
            // become a primitive simply because another use was arithmetic.
            foreach(var variable in instruction.Operands.SelectMany(Locals).Distinct())
                if(domains.ContainsKey(variable) && !handled.Contains(variable))domains[variable]=0;
        }
        var edges=variables.ToDictionary(v=>v,_=>new List<int>());
        for(var i=0;i<relations.Count;i++)
        {
            if(relations[i].Left.Local is { } a)edges[a].Add(i);
            if(relations[i].Right.Local is { } b)edges[b].Add(i);
        }
        var pending=new Queue<int>(Enumerable.Range(0,relations.Count));var queued=Enumerable.Repeat(true,relations.Count).ToArray();
        int Mask(Value value)=>value.Local!=null?domains[value.Local]:value.Fixed;
        void Narrow(LocalVariable? variable,int mask)
        {
            if(variable==null)return;
            var next=domains[variable]&mask;if(next==domains[variable])return;domains[variable]=next;
            foreach(var edge in edges[variable])if(!queued[edge]){queued[edge]=true;pending.Enqueue(edge);}
        }
        while(pending.TryDequeue(out var edge))
        {
            queued[edge]=false;var r=relations[edge];var common=Mask(r.Left)&Mask(r.Right)&r.Allowed;
            Narrow(r.Left.Local,common);Narrow(r.Right.Local,common);
        }
        var promoted=new HashSet<LocalVariable>();var t=method.AppContext.SystemTypes;
        foreach(var (variable,mask) in domains)
        {
            variable.Type=mask switch {I4=>t.SystemInt32Type,I8=>t.SystemInt64Type,R4=>t.SystemSingleType,R8=>t.SystemDoubleType,_=>null};
            if(variable.Type!=null)promoted.Add(variable);
        }
        foreach(var instruction in instructions)
        {
            if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable target,Immediate {Value:0}]}
                && promoted.Contains(target) && Kind(target.Type) is R4 or R8)
                instruction.SetOperand(1,Kind(target.Type)==R4?new FloatLiteral(0):new DoubleLiteral(0));
            if(instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
                && instruction.Destination is LocalVariable target2 && promoted.Contains(target2) && Kind(target2.Type) is R4 or R8)
                for(var p=1;p<instruction.Operands.Count;p++)
                    if(instruction.Operands[p] is Immediate {Value:0})
                        instruction.SetOperand(p,Kind(target2.Type)==R4?new FloatLiteral(0):new DoubleLiteral(0));
            if(instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess or OpCode.CheckGreater
                or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual)
                for(var p=1;p<instruction.Operands.Count;p++)
                    if(instruction.Operands[p] is Immediate {Value:0}
                        && instruction.Operands[3-p] is LocalVariable other && promoted.Contains(other) && Kind(other.Type) is R4 or R8)
                        instruction.SetOperand(p,Kind(other.Type)==R4?new FloatLiteral(0):new DoubleLiteral(0));
            if(instruction.Destination is LocalVariable integer && promoted.Contains(integer) && Kind(integer.Type)==I4
                && instruction.OpCode is OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.And or OpCode.Or or OpCode.Xor)
                for(var p=1;p<instruction.Operands.Count;p++)
                    if(instruction.Operands[p] is Immediate {Value:>int.MaxValue and <=uint.MaxValue} bits)
                        instruction.SetOperand(p,new Immediate(unchecked((int)bits.Value)));
        }
        return promoted.Count;
    }

    private static IEnumerable<LocalVariable> Locals(IOperand operand)
    {
        switch(operand)
        {
            case LocalVariable local:yield return local;break;
            case MemoryOperand m:
                if(m.Base!=null)foreach(var v in Locals(m.Base))yield return v;
                if(m.Index!=null)foreach(var v in Locals(m.Index))yield return v;break;
            case FieldReference f:
                if(f.Local!=null)yield return f.Local;
                if(f.Parent!=null)foreach(var v in Locals(f.Parent))yield return v;break;
            case ArrayAccess a:
                yield return a.Array;foreach(var v in Locals(a.Index))yield return v;break;
            case ArrayLength a:yield return a.Array;break;
            case AddressOf a:foreach(var v in Locals(a.Target))yield return v;break;
        }
    }
}
