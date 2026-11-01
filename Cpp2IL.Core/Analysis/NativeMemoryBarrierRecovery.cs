using System;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Complete original primary1286: AA3468 is exactly DMB ISH; RET.
// Caller primary1296 proves the barrier precedes the release store. NEVER NOP
// the operation: bind the exact existing static Thread.MemoryBarrier member.
public static class NativeMemoryBarrierRecovery
{
    private const ulong Address=0xAA3468;
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<bool>> Profiles=new();

    internal static bool Matches(ReadOnlySpan<byte> bytes)
        =>bytes.SequenceEqual(new byte[]{0xbf,0x3b,0x03,0xd5,0xc0,0x03,0x5f,0xd6});

    private static bool Supports(ApplicationAnalysisContext app)
        =>app.Binary.PointerSizeBytes==8 && app.UnityVersion.Major==2018 && app.UnityVersion.Minor==4
            && Profiles.GetValue(app,owner=>new Lazy<bool>(()=>
            {
                if(!CheckedUnboxRecovery.Supports(owner) || owner.Metadata.BaseStream is not MemoryStream stream
                    || !string.Equals(Convert.ToHexString(SHA256.HashData(stream.ToArray())),
                        "78e2ee2e6738511c08c9a0c0bdc1304c8d4f21740dc19958bb8b6690cfe3140e",StringComparison.OrdinalIgnoreCase)
                    || !owner.Binary.TryMapVirtualAddressToRaw(Address,out var raw)
                    || raw<0 || raw>owner.Binary.RawLength-8)return false;
                return Matches(owner.Binary.GetRawBinaryContent().Slice((int)raw,8));
            })).Value;

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not {} graph
            || !graph.Instructions.Any(i=>i.IsCall && i.Operands.Count>0 && i.Operands[0] is Immediate {UnsignedValue:Address})
            || !Supports(method.AppContext) || method.AppContext.MethodsByAddress.ContainsKey(Address))return 0;
        var targets=method.AppContext.Assemblies.Where(a=>a.Name=="mscorlib").SelectMany(a=>a.Types)
            .Where(t=>t.FullName=="System.Threading.Thread").SelectMany(t=>t.Methods)
            .Where(ValidTarget).Take(2).ToArray();
        return targets.Length==1?Rewrite(method,targets[0],address=>address==Address):0;
    }

    private static bool ValidTarget(MethodAnalysisContext target)
        =>target.Name=="MemoryBarrier" && target.IsStatic && target.IsVoid && target.Parameters.Count==0
            && target.GenericParameters.Count==0 && target.DeclaringType is {FullName:"System.Threading.Thread"} owner
            && owner.DeclaringAssembly.Name=="mscorlib";

    // Detached shape entry; production authenticates the whole native image,
    // metadata AND exact complete helper above. This never certifies a method.
    internal static int Rewrite(MethodAnalysisContext method,MethodAnalysisContext target,Func<ulong,bool> prove)
    {
        if(!ValidTarget(target) || ReferenceEquals(method,target)
            || method.UnderlyingPointer!=0 && method.UnderlyingPointer==target.UnderlyingPointer
            || method.ControlFlowGraph is not {} graph)return 0;
        var changed=0;
        foreach(var call in graph.Instructions.AsEnumerable().Reverse().ToArray())
        {
            if(!call.IsCall || call.Operands.Count==0 || call.Operands[0] is not Immediate address
                || !prove(address.UnsignedValue) || call.ImplicitDefinition!=null
                || call.NativeVirtualDispatch || call.NativeNullCheckedCall)continue;
            var skip=1;
            if(call.OpCode==OpCode.Call)
            {
                if(call.Operands.Count<2 || call.Operands[1] is not LocalVariable result
                    || graph.Instructions.Any(i=>!ReferenceEquals(i,call) && i.Operands.Any(o=>ForwardNullCheckRecovery.Uses(o,result))))continue;
                skip=2;
            }
            if(call.Operands.Skip(skip).Any(o=>o is not (LocalVariable or Immediate or TypeAnalysisContext
                or FloatLiteral or DoubleLiteral or StringLiteral)))continue;
            call.OpCode=OpCode.CallVoid;call.SetOperands(target);call.NativeDirectCallTarget=0;
            changed++;
        }
        return changed;
    }
}
