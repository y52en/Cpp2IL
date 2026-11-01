using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A native W definition also zeroes the X register's upper half. Model that
// bit contract as UInt32, retaining signedness on EACH comparison/consumer.
// Never infer a reference, an incoming argument or an unknown-width operation.
public static class NativeWord32LoopRecovery
{
    private static bool Unknown(LocalVariable local,MethodAnalysisContext method)=>local.Type==null
        && !local.IsThis && !local.IsReturn && !local.IsReturnBuffer && !local.IsMethodInfo
        && local.ParameterIndex<0 && !method.ParameterLocals.Contains(local);

    private static bool Word(IOperand value,LocalVariable local)=>ReferenceEquals(value,local)
        || value is Immediate {Value:>=int.MinValue and <=uint.MaxValue}
        || value is LocalVariable {Type.FullName:"System.Int32" or "System.UInt32"};

    private static IEnumerable<IOperand> Inputs(Instruction instruction)
    {
        // Skip only the destination SLOT, not every occurrence of the same
        // local: i=i+1 still reads i. Nested array/field destinations are uses.
        var destination=instruction.Destination;
        var slot=instruction.OpCode==OpCode.Call?1:0;
        for(var index=0;index<instruction.Operands.Count;index++)
            if(!(index==slot && destination is LocalVariable && ReferenceEquals(instruction.Operands[index],destination)))
                yield return instruction.Operands[index];
    }

    private static bool IndexOnly(IOperand operand,LocalVariable local)=>operand switch
    {
        ArrayAccess access=>!ReferenceEquals(access.Array,local) && ReferenceEquals(access.Index,local)
            && access.Array.Type is SzArrayTypeAnalysisContext,
        AddressOf {Target:ArrayAccess access}=>IndexOnly(access,local),
        _=>false,
    };

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph || graph.Blocks.Count>512 || graph.Instructions.Count()>16384
            || method.AppContext.Binary.PointerSizeBytes!=8)return 0;
        var all=graph.Instructions.ToArray();
        var candidates=all.Where(i=>i.NativeArithmeticSize==4 && i.Destination is LocalVariable)
            .Select(i=>(LocalVariable)i.Destination!).Distinct().ToArray();
        var changed=0;
        foreach(var local in candidates)if(TryType(method,local,all))changed++;
        return changed;
    }

    internal static bool TryType(MethodAnalysisContext method,LocalVariable local,Instruction[] all)
    {
        if(!Unknown(local,method) || method.ControlFlowGraph is not {} graph)return false;
        var definitions=all.Where(i=>ReferenceEquals(i.Destination,local)).ToArray();
        var initializers=definitions.Where(i=>i is {OpCode:OpCode.Move,Operands:[_,Immediate {Value:>=0 and <=uint.MaxValue}]}).ToArray();
        if(initializers.Length!=1 || definitions.Length<2)return false;
        var initial=initializers[0];
        if(definitions.Any(i=>!ReferenceEquals(i,initial) && !(i.NativeArithmeticSize==4 && i.NativeFloatingPointSize==0
            && i.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
            && i.Operands.Count==3 && i.Operands.Skip(1).All(o=>Word(o,local)))))return false;
        var wide=new HashSet<LocalVariable>();
        foreach(var instruction in all)
        {
            var reads=Inputs(instruction).Where(o=>ForwardNullCheckRecovery.Uses(o,local)).ToArray();
            if(reads.Length==0)continue;
            if(!ForwardNullCheckRecovery.DefinitionDominates(graph,initial,instruction))return false;
            if(reads.All(o=>IndexOnly(o,local)))continue;
            if(reads.Any(o=>!ReferenceEquals(o,local)))return false;
            if(instruction is {OpCode:OpCode.NumericConvert,NativeIntegerSourceView:true,
                Operands:[_,TypeAnalysisContext {FullName:"System.SByte" or "System.Byte" or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32"},
                    TypeAnalysisContext {FullName:"System.UInt64"},var bits]}
                && ReferenceEquals(bits,local))continue;
            if(instruction.NativeArithmeticSize==4 && instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
                && ReferenceEquals(instruction.Destination,local) && instruction.Operands.Skip(1).All(o=>Word(o,local)))continue;
            if(instruction.NativeComparisonSize==4 && instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                or OpCode.CheckLess or OpCode.CheckLessOrEqual or OpCode.CheckGreater or OpCode.CheckGreaterOrEqual
                && instruction.Operands.Count==3 && instruction.Operands.Skip(1).All(o=>Word(o,local)))continue;
            if(instruction is {OpCode:OpCode.Multiply,NativeArithmeticSize:8,NativeMultiplyInputSize:8,Operands:[LocalVariable product,var left,var right]}
                && Word(left,local) && Word(right,local)
                // Other signed I4 operands would require their OWN native X
                // zero-extension proof. Do not assume it from managed Int32.
                && new[]{left,right}.All(o=>ReferenceEquals(o,local) || o is Immediate {Value:>=0 and <=uint.MaxValue})
                && Unknown(product,method) && all.Count(i=>ReferenceEquals(i.Destination,product))==1)
            {
                var safe=true;
                foreach(var use in all)
                {
                    var operands=Inputs(use).Where(o=>ForwardNullCheckRecovery.Uses(o,product)).ToArray();
                    if(operands.Length==0)continue;
                    // Only an explicit full-width array-base + numeric offset.
                    // Preserve the address operation and all later memory effects.
                    if(operands.Any(o=>!ReferenceEquals(o,product)) || use is not
                        {OpCode:OpCode.Add,NativeArithmeticSize:8,Operands:[LocalVariable {Type:null},var a,var b]}
                        || !(ReferenceEquals(a,product) && b is LocalVariable {Type:SzArrayTypeAnalysisContext}
                            || ReferenceEquals(b,product) && a is LocalVariable {Type:SzArrayTypeAnalysisContext})
                        || !ForwardNullCheckRecovery.DefinitionDominates(graph,instruction,use))
                    {safe=false;break;}
                }
                if(!safe)return false;
                wide.Add(product);continue;
            }
            return false;
        }
        // Mutate only after ALL definitions, consumers and extensions pass.
        local.Type=method.AppContext.SystemTypes.SystemUInt32Type;
        foreach(var product in wide)product.Type=method.AppContext.SystemTypes.SystemUInt64Type;
        return true;
    }
}
