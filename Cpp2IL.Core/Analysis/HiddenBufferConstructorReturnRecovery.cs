using System.Linq;
using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// A native void constructor can initialize the caller's incoming X8 return
// storage. Its physical X0 result is undefined, not the constructed value.
public static class HiddenBufferConstructorReturnRecovery
{
    public static bool Run(MethodAnalysisContext method)
        => method.AppContext.InstructionSet is NewArmV8InstructionSet
            && method.AppContext.Binary.PointerSizeBytes==8 && Recover(method);

    public static bool Recover(MethodAnalysisContext method)
    {
        var cfg=method.ControlFlowGraph;
        if(cfg==null)return false;
        var scoped=SharedGenericReturnLayout.TryGet(method);
        var size=ClosedGenericValueLayout.TryGet(method.ReturnType,8)?.Size??scoped?.Size??0;
        var layout=ClosedGenericValueLayout.Fields(method.ReturnType,8)??scoped?.Fields;
        if(size<=16 || layout==null)return false;
        var blocks=cfg.Blocks.Where(b=>b.Instructions.Any(i=>i.OpCode!=OpCode.Nop)).ToArray();
        if(blocks.Length!=1 || blocks[0].Successors.Count!=1
            || !ReferenceEquals(blocks[0].Successors[0],cfg.ExitBlock))return false;
        var instructions=blocks[0].Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(instructions.Length!=layout.Count+2
            || instructions[^2] is not {OpCode:OpCode.Call,Operands:[MethodAnalysisContext
                {Name:".ctor",IsStatic:false,IsVoid:true} target,LocalVariable discarded,LocalVariable buffer,..]} call
            || instructions[^1] is not {OpCode:OpCode.Return,Operands:[var returned]} ret
            || !ReferenceEquals(discarded,returned) || ReferenceEquals(buffer,discarded)
            || buffer.Register is not {Name:"X8",Version:-1}
            || !buffer.IsReturnBuffer
            || !ReferenceEquals(buffer.Type,method.ReturnType)
            || !TrivialConstructorRecovery.SameType(target.DeclaringType,method.ReturnType)
            || call.Operands.Count!=target.Parameters.Count+3
            || call.Operands.Skip(3).Any(o=>ReferenceEquals(o,buffer)||ReferenceEquals(o,discarded)))return false;
        var remaining=new HashSet<FieldAnalysisContext>(layout.Select(f=>BaseField(f.Field)));
        foreach(var instruction in instructions.Take(instructions.Length-2))
        {
            if(instruction is not {OpCode:OpCode.Move,Operands:[FieldReference {Parent:null} field,Immediate {Value:0}]}
                || !ReferenceEquals(field.Local,buffer))return false;
            var storage=layout.Where(f=>ReferenceEquals(BaseField(f.Field),BaseField(field.Field))).ToArray();
            if(storage.Length!=1 || field.Offset!=storage[0].Offset
                || instruction.NativeWriteSize!=storage[0].Size
                || !remaining.Remove(BaseField(field.Field)))return false;
        }
        if(remaining.Count!=0)return false;
        foreach(var instruction in instructions.Take(instructions.Length-2))
            if(instruction.Operands[0] is FieldReference {Field.FieldType:GenericParameterTypeAnalysisContext parameter})
                instruction.SetOperand(1,new DefaultStructValue(parameter));
        var args=call.Operands.Skip(3).ToArray();
        call.OpCode=OpCode.CallVoid;
        call.SetOperands(new List<IOperand>{target,new AddressOf(buffer)}.Concat(args).ToList());
        ret.SetOperands(buffer);buffer.IsReturn=true;discarded.IsReturn=false;
        return true;
    }

    private static FieldAnalysisContext BaseField(FieldAnalysisContext field)
        => field is ConcreteGenericFieldAnalysisContext concrete?concrete.BaseFieldContext:field;
}
