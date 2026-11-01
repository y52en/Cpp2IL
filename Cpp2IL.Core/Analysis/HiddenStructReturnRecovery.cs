using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Run after stack normalization, before SSA. An ARM64 large-struct return
// writes to the caller's X8 buffer, not to X0. Only a proven stack address and
// a unique metadata signature authorize replacing the synthetic destination.
public static class HiddenStructReturnRecovery
{
    internal static MethodAnalysisContext? ExactZeroArgumentTarget(MethodAnalysisContext caller,Block block,int before,
        ulong address,IReadOnlyList<MethodAnalysisContext> targets,
        System.Func<ulong,MethodAnalysisContext?>? metadata=null,System.Func<ulong,ulong?>? got=null)
    {
        if(targets.Count==0 || targets.Any(target=>target.Parameters.Count!=0)
            || targets.Any(target=>target.IsStatic!=targets[0].IsStatic))return null;
        var infoRegister=new Register(null,targets[0].IsStatic?"X0":"X1");
        var method=RawHiddenMethodInfoRecovery.Resolve(caller,block,before,infoRegister,metadata,got);
        if(method==null || System.Object.ReferenceEquals(method,caller) || method.Parameters.Count!=0
            || method.IsStatic!=targets[0].IsStatic || method.ReturnType.HasAnyGenericParameters())return null;
        static MethodAnalysisContext Base(MethodAnalysisContext value)
            =>value is ConcreteGenericMethodAnalysisContext concrete?concrete.BaseMethodContext:value;
        if(!targets.Any(target=>System.Object.ReferenceEquals(Base(target),Base(method))))return null;
        // MetadataUsage may hold the exact real MethodSpec without copying its
        // native pointer. Require the existing registered full-identity proof;
        // a display name or an inferred return size cannot authorize this path.
        return MetadataResolver.UnmappedNativeEntryMatches(method,address)?method:null;
    }

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet) return false;
        var graph=method.ControlFlowGraph!;
        if(method.AppContext.InstructionSet.CallingConventionResolver is not Arm64CallingConventionResolver resolver)return false;
        var changed=false;
        foreach(var block in graph.Blocks)
        foreach(var call in block.Instructions)
        {
            if(call.OpCode!=OpCode.Call || call.Operands[0] is not Immediate address
                || !method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue,out var targets)
                || targets.Count==0) continue;
            // ICF/shared generic aliases do not identify a declaring type, but
            // ALL candidates can prove the same native result-storage ABI.
            // Leave the concrete target/type to the separate MethodInfo pass.
            var signature=targets[0];
            var size=resolver.ReturnStorageSize(signature);
            var unanimous=resolver.ReturnsViaHiddenBuffer(signature)
                && targets.All(target=>resolver.ReturnsViaHiddenBuffer(target)
                    && resolver.HiddenReturnBufferRegister(target)?.Name==resolver.HiddenReturnBufferRegister(signature)?.Name
                    && resolver.ReturnStorageSize(target)==size);
            if(!unanimous)
            {
                var exact=ExactZeroArgumentTarget(method,block,block.Instructions.IndexOf(call),address.UnsignedValue,targets);
                if(exact==null||!resolver.ReturnsViaHiddenBuffer(exact))continue;
                signature=exact;
                size=resolver.ReturnStorageSize(signature);
            }
            var buffer=resolver.HiddenReturnBufferRegister(signature);
            if(size is <=16 or >4096 || buffer is not { } register
                || unanimous && targets.Any(target=>!resolver.ReturnsViaHiddenBuffer(target)
                    || resolver.HiddenReturnBufferRegister(target)?.Name!=register.Name
                    || resolver.ReturnStorageSize(target)!=size)
                || ResolveStackAddress(block,block.Instructions.IndexOf(call),register) is not { } storage) continue;
            call.Destination=storage;
            call.ImplicitDefinition=new Register(null,"X0");
            call.NativeReturnStorageSize=(int)size;
            changed=true;
        }
        return changed;
    }

    public static Register? ResolveStackAddress(Block block,int before,Register pointer)
        => Resolve(block,before,pointer,new HashSet<Block>(),128);

    private static Register? Resolve(Block block,int before,Register pointer,HashSet<Block> seen,int remaining)
    {
        if(remaining<=0 || !seen.Add(block)) return null;
        for(var i=before-1;i>=0;i--)
        {
            var instruction=block.Instructions[i];
            if(instruction.Destination is Register written && written.Name==pointer.Name)
            {
                if(instruction is {OpCode:OpCode.Move,Operands:[_,AddressOf {Target:Register storage}]}
                    && storage.Name.StartsWith("stack_",System.StringComparison.Ordinal)) return storage;
                if(instruction is {OpCode:OpCode.Move,Operands:[_,Register source]})
                    // The copy reads the source at this instruction, not at the
                    // eventual call. Revisit this block at an earlier position.
                    return Resolve(block,i,source,new HashSet<Block>(),remaining-1);
                return null;
            }
            if(instruction.OpCode is OpCode.NotImplemented or OpCode.Invalid or OpCode.Interrupt) return null;
            if((instruction.IsCall || instruction.OpCode==OpCode.IndirectCall) && Volatile(pointer)) return null;
        }
        if(block.Predecessors.Count!=1) return null;
        var predecessor=block.Predecessors[0];
        return Resolve(predecessor,predecessor.Instructions.Count,pointer,seen,remaining-1);
    }

    private static bool Volatile(Register register)
        => register.Name.StartsWith("V",System.StringComparison.Ordinal)
           || register.Name.StartsWith("X",System.StringComparison.Ordinal)
               && int.TryParse(register.Name.Substring(1),out var number) && number<=18;
}
