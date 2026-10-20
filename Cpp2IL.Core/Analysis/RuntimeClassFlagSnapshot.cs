using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// Recognition only: do not globally replace or move a load. A retained byte
// snapshot can identify the same runtime flag as the older inlined pattern.
internal static class RuntimeClassFlagSnapshot
{
    public static MemoryOperand? Resolve(ISILControlFlowGraph cfg,Block guard,Instruction consumer,IOperand operand)
    {
        if(operand is MemoryOperand direct)return direct;
        if(operand is not LocalVariable snapshot)return null;
        var definitions=cfg.Instructions.Where(i=>ReferenceEquals(i.Destination,snapshot)).ToArray();
        if(definitions.Length!=1 || definitions[0] is not
            {OpCode:OpCode.Move,Operands:[_,MemoryOperand memory],NativeReadSize:1} load
            || !guard.Instructions.Contains(load)
            || guard.Instructions.IndexOf(load)>=guard.Instructions.IndexOf(consumer))return null;
        return memory;
    }
}
