using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A native first-field load shares the synthetic stack register with the
// entire returned struct. The managed callee's exact parameter type can
// distinguish them. Never project untyped uses or whole-struct arguments.
public static class StackFieldZeroRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph=method.ControlFlowGraph!;
        var definitions=graph.Instructions.Where(i=>i.Destination is LocalVariable)
            .GroupBy(i=>(LocalVariable)i.Destination!).Where(g=>g.Count()==1)
            .ToDictionary(g=>g.Key,g=>g.Single());
        DominatorInfo? dominance=null;
        var changed=false;
        foreach(var block in graph.Blocks)
        foreach(var call in block.Instructions)
        {
            if(!call.IsCall || call.Operands[0] is not MethodAnalysisContext target) continue;
            var first=(call.OpCode==OpCode.CallVoid?1:2)+(target.IsStatic?0:1);
            for(var p=0;p<target.Parameters.Count && first+p<call.Operands.Count;p++)
            {
                if(call.Operands[first+p] is not LocalVariable argument
                    || Storage(argument,definitions) is not { } storage) continue;
                // A scalar copied before a by-address mutation must not turn
                // into a later live field read. Reject mutable/escaped storage
                // rather than assuming these calls cannot change it.
                if(graph.Instructions.Any(i=>i is {OpCode:OpCode.Move,Operands:[FieldReference written,..]}
                        && Storage(written.Local,definitions)==storage
                    || i.Operands.Any(o=>o is AddressOf {Target:LocalVariable addressed}
                            && Storage(addressed,definitions)==storage
                        || o is AddressOf {Target:FieldReference addressedField}
                            && Storage(addressedField.Local,definitions)==storage))) continue;
                var expected=target.Parameters[p].ParameterType;
                // Matching the complete struct signature must retain the value,
                // not silently reinterpret it as its first field.
                if(expected==storage.Type || expected is ByRefTypeAnalysisContext) continue;
                var fields=storage.Type!.Fields.Where(f=>!f.IsStatic && f.Offset==0).ToArray();
                if(fields.Length!=1 || fields[0].FieldType!=expected) continue;
                var writer=definitions[storage];
                var writerBlock=graph.Blocks.Single(b=>b.Instructions.Contains(writer));
                var preceding=writerBlock==block
                    ? block.Instructions.IndexOf(writer)<block.Instructions.IndexOf(call)
                    : (dominance??=new DominatorInfo(graph)).Dominates(writerBlock,block);
                if(!preceding) continue;
                call.SetOperand(first+p,new FieldReference(fields[0],storage,0));
                changed=true;
            }
        }
        return changed;
    }

    private static LocalVariable? Storage(LocalVariable local,Dictionary<LocalVariable,Instruction> definitions)
    {
        var seen=new HashSet<LocalVariable>();
        while(seen.Add(local) && definitions.TryGetValue(local,out var definition))
        {
            if(definition is {OpCode:OpCode.Call,Operands:[MethodAnalysisContext target, ..]}
                && target.ReturnType==local.Type && local.Type?.IsValueType==true
                && local.Register.Name.StartsWith("stack_",System.StringComparison.Ordinal)) return local;
            if(definition is not {OpCode:OpCode.Move,Operands:[_,LocalVariable source]}) return null;
            local=source;
        }
        return null;
    }
}
