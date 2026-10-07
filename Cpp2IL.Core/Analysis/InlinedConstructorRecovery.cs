using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Reconstitute only constructors whose complete native analysis consists of
// Object's no-op constructor followed by distinct this-field assignments.
public static class InlinedConstructorRecovery
{
    public const string CacheKey = "PureFieldConstructorTemplates";
    public sealed record Assignment(FieldAnalysisContext Field, int Parameter);
    public sealed record Template(MethodAnalysisContext Constructor, IReadOnlyList<Assignment> Assignments);

    public static Template? Extract(MethodAnalysisContext ctor)
    {
        if (ctor.Name != ".ctor" || ctor.IsStatic || ctor.DeclaringType?.BaseType?.FullName != "System.Object"
            || ctor.ControlFlowGraph == null || ctor.Parameters.Count == 0) return null;
        var parameters = ctor.ParameterLocals.Where(l => !l.IsThis && !l.IsMethodInfo).ToList();
        if (parameters.Count != ctor.Parameters.Count) return null;
        if (ctor.ControlFlowGraph.Blocks.Any(b => b.Successors.Count > 1)) return null;
        var visited = new HashSet<Graphs.Block>();
        var block = ctor.ControlFlowGraph.EntryBlock;
        while (block.Successors.Count == 1)
        {
            if (!visited.Add(block)) return null;
            block = block.Successors[0];
        }
        var result = new List<Assignment>();
        var baseCalls = 0;
        var returned = false;
        foreach (var instruction in ctor.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
            if (instruction.OpCode == OpCode.Return && instruction.Operands.Count == 0) { returned = true; continue; }
            if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor", DeclaringType.FullName: "System.Object", Parameters.Count: 0 }, LocalVariable { IsThis: true }] })
            { if (++baseCalls > 1) return null; continue; }
            if (instruction is not { OpCode: OpCode.Move, Operands: [FieldReference field, LocalVariable source] }
                || !field.Local.IsThis || field.Field.IsStatic || field.Field.DeclaringType != ctor.DeclaringType)
                return null;
            var parameter = parameters.IndexOf(source);
            if (parameter < 0 || result.Any(a => a.Field == field.Field)) return null;
            result.Add(new(field.Field, parameter));
        }
        if (!returned || result.Count == 0 || Enumerable.Range(0,parameters.Count).Any(i => result.All(a => a.Parameter != i))) return null;
        return new(ctor, result.ToArray());
    }

    public static void Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph == null) return;
        foreach (var allocation in method.ControlFlowGraph.Instructions.ToArray())
            if (allocation is { OpCode: OpCode.Newobj, Operands: [LocalVariable _, TypeAnalysisContext type] }
                && type.GetExtraData<Template[]>(CacheKey) is { Length: > 0 } templates)
                Recover(method, allocation, templates);
    }

    public static bool Recover(MethodAnalysisContext method, Instruction allocation, IReadOnlyList<Template> templates)
    {
        if (allocation is not { OpCode: OpCode.Newobj, Operands: [LocalVariable obj, TypeAnalysisContext type] }
            || type.IsValueType || type.BaseType?.FullName != "System.Object") return false;
        var instructions = method.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(allocation);
        if (index < 0) return false;
        var allocationBlock = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(allocation));
        var scan = allocationBlock.Instructions.Skip(allocationBlock.Instructions.IndexOf(allocation)+1).ToList();
        var visited = new HashSet<Block> {allocationBlock};
        var current = allocationBlock;
        // BFS instruction order is NOT execution order across branches. Only a
        // single-entry straight-line continuation belongs to this initialization.
        while (current.Successors.Count == 1 && current.Successors[0].Predecessors.Count == 1
            && visited.Add(current.Successors[0]))
        { current = current.Successors[0]; scan.AddRange(current.Instructions); }
        DominatorInfo? dominance = null;
        var aliases = new HashSet<LocalVariable> {obj};
        Instruction? baseCall = null;
        var stores = new List<Instruction>();
        var matches = new List<(Template Template, IOperand[] Args)>();
        foreach (var instruction in scan)
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable alias, LocalVariable source] } && aliases.Contains(source))
            { aliases.Add(alias); continue; }
            if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor", DeclaringType.FullName: "System.Object", Parameters.Count: 0 }, LocalVariable receiver] }
                && aliases.Contains(receiver) && baseCall == null && stores.Count == 0)
            { baseCall = instruction; continue; }
            if (baseCall == null || instruction is not { OpCode: OpCode.Move, Operands: [FieldReference field, var value] }
                || !aliases.Contains(field.Local) || field.Field.DeclaringType != type || field.Field.IsStatic
                || stores.Any(s => ((FieldReference)s.Operands[0]).Field == field.Field)
                || !AvailableBeforeAllocation(value, method, instructions, index, allocationBlock, ref dominance, aliases)) break;
            stores.Add(instruction);
            matches.Clear();
            foreach (var template in templates.Where(t => t.Constructor.DeclaringType == type && t.Assignments.Count == stores.Count))
            {
                var args = new IOperand[template.Constructor.Parameters.Count];
                var valid = true;
                foreach (var assignment in template.Assignments)
                {
                    var store = stores.SingleOrDefault(s => ((FieldReference)s.Operands[0]).Field == assignment.Field);
                    if (store == null) { valid = false; break; }
                    var argument = store.Operands[1];
                    if (args[assignment.Parameter] is { } previous && !SameValue(previous, argument)) { valid = false; break; }
                    args[assignment.Parameter] = argument;
                }
                if (valid && args.All(a => a != null)) matches.Add((template,args));
            }
            if (matches.Count > 0) break;
        }
        if (baseCall == null || matches.Count != 1) return false;
        var match = matches[0];
        baseCall.SetOperands(new List<IOperand> {match.Template.Constructor,obj}.Concat(match.Args).ToList());
        foreach (var store in stores) { store.OpCode = OpCode.Nop; store.SetOperands(); }
        return true;
    }

    private static bool AvailableBeforeAllocation(IOperand value, MethodAnalysisContext method,
        List<Instruction> instructions, int allocationIndex, Block allocationBlock,
        ref DominatorInfo? dominance, ISet<LocalVariable> aliases)
    {
        if (value is Immediate or FloatLiteral or DoubleLiteral or StringLiteral) return true;
        if (value is not LocalVariable local || aliases.Contains(local)) return false;
        var definitions = instructions.Select((i,n)=>(i,n)).Where(x => ReferenceEquals(x.i.Destination,local)).ToList();
        if (definitions.Count == 0) return method.ParameterLocals.Contains(local);
        // A loop local can be assigned again AFTER initialization. We load its
        // current value at allocation, not a frozen SSA version. The scanned
        // initialization contains no writes to argument locals, so subsequent
        // loop increments cannot change any value moved to the constructor call.
        foreach (var definition in definitions.Where(d => d.n < allocationIndex))
        {
            var definitionBlock = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(definition.i));
            if (definitionBlock == allocationBlock) return true;
            dominance ??= new DominatorInfo(method.ControlFlowGraph);
            if (dominance.Dominates(definitionBlock, allocationBlock)) return true;
        }
        return false;
    }

    private static bool SameValue(IOperand a, IOperand b) => ReferenceEquals(a,b) || (a,b) switch
    {
        (Immediate x,Immediate y) => x.Value == y.Value,
        (FloatLiteral x,FloatLiteral y) => x.Value.Equals(y.Value),
        (DoubleLiteral x,DoubleLiteral y) => x.Value.Equals(y.Value),
        (StringLiteral x,StringLiteral y) => x.Value == y.Value,
        _ => false
    };
}
