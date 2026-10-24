using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// Optional original-native proof input. A complete boxed leaf and an actual
// complete unboxed counterpart must differ ONLY in canonical receiver offsets.
// Normalize the coordinate before SSA, not metadata or executable bytes.
public static class InlineBoxedHfaRecovery
{
    private sealed record Catalog(Dictionary<ulong,JsonElement> Rows);
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext,Lazy<Catalog?>> Catalogs=new();

    public static int Run(MethodAnalysisContext method)
    {
        if(string.IsNullOrEmpty(Environment.GetEnvironmentVariable("CPP2IL_INLINE_ADJUSTOR_PROOFS"))
            || method.IsStatic || method.DeclaringType is not {} owner || owner.HasAnyGenericParameters()
            || owner.IsGenericInstance || (Arm64HfaLayout.Fields(owner)==null && !IntegralLeafCandidate(method))
            || method.Definition==null)return 0;
        var catalog=Catalogs.GetValue(method.AppContext,app=>new(()=>Load(app))).Value;
        if(catalog==null || !catalog.Rows.TryGetValue(method.UnderlyingPointer,out var row))return 0;
        var aliases=row.GetProperty("metadata_aliases").EnumerateArray().Where(a=>
            a.GetProperty("owner").GetString()==owner.FullName && a.GetProperty("assembly").GetString()==owner.DeclaringAssembly.Name
            && a.GetProperty("method").GetString()==method.FullName
            && a.GetProperty("token").GetUInt32()==method.Definition.token
            && a.GetProperty("return_type").GetString()==method.ReturnType.FullName
            && a.GetProperty("parameters").EnumerateArray().Select(p=>p.GetString()).SequenceEqual(method.Parameters.Select(p=>p.ParameterType.FullName)))
            .ToArray();
        if(aliases.Length!=1 || aliases[0].GetProperty("size").GetInt64()!=TypeSizes.UnboxedSize(owner,8))return 0;
        var recorded=aliases[0].GetProperty("fields").EnumerateArray().Select(f=>
            (f.GetProperty("Name").GetString(),f.GetProperty("Offset").GetInt32(),f.GetProperty("type").GetString())).ToArray();
        if(!recorded.SequenceEqual(owner.Fields.Where(f=>!f.IsStatic).Select(f=>((string?)f.Name,f.Offset,(string?)f.FieldType.FullName))))return 0;
        var original=Convert.FromHexString(row.GetProperty("native_bytes").GetString()!);
        var expected=Convert.FromHexString(row.GetProperty("adjusted_bytes").GetString()!);
        if(!method.RawBytes.ToArray().SequenceEqual(original))return 0;
        var peers=row.GetProperty("exact_fde_counterparts").EnumerateArray().Select(p=>
            Convert.ToUInt64(p.GetString()!.Substring(2),16)).ToArray();
        if(peers.Length==0 || peers.Distinct().Count()!=peers.Length)return 0;
        var binary=method.AppContext.Binary;
        foreach(var peer in peers)
        {
            if(!binary.TryMapVirtualAddressToRaw(peer,out var raw) || raw<0 || raw>binary.RawLength-expected.Length
                || !binary.GetRawBinaryContent().Slice(checked((int)raw),expected.Length).SequenceEqual(expected))return 0;
        }
        return Recover(method,original,expected);
    }

    private static Catalog? Load(ApplicationAnalysisContext app)
    {
        var path=Environment.GetEnvironmentVariable("CPP2IL_INLINE_ADJUSTOR_PROOFS");
        if(string.IsNullOrEmpty(path))return null;
        var bytes=File.ReadAllBytes(path);
        if(bytes.Length>16*1024*1024 || !string.Equals(Convert.ToHexString(SHA256.HashData(bytes)),
                Environment.GetEnvironmentVariable("CPP2IL_INLINE_ADJUSTOR_PROOF_SHA256"),StringComparison.OrdinalIgnoreCase))
            throw new InvalidOperationException("hash-pinned inline adjustor proof required");
        using var document=JsonDocument.Parse(bytes);var root=document.RootElement;
        if(!IdentityMatches(app,root))
            throw new InvalidOperationException("original loaded image/metadata differ from inline adjustor proof");
        var rows=new Dictionary<ulong,JsonElement>();
        foreach(var row in root.GetProperty("rows").EnumerateArray())
        {
            if(row.GetProperty("status").GetString()!="complete_native_counterpart_found")continue;
            if(!rows.TryAdd(Convert.ToUInt64(row.GetProperty("rva").GetString()!.Substring(2),16),row.Clone()))
                throw new InvalidOperationException("ambiguous inline adjustor proof entry");
        }
        return new(rows);
    }

    internal static bool IdentityMatches(ApplicationAnalysisContext app,JsonElement root)
        => !(root.GetProperty("schema").GetString()!="inline-adjustor-native-counterparts-v1"
            || root.GetProperty("diagnostic_only").GetBoolean()!=true || root.GetProperty("adoption_allowed").GetBoolean()!=false
            || !string.Equals(root.GetProperty("loaded_image_sha256").GetString(),
                Convert.ToHexString(SHA256.HashData(app.Binary.GetRawBinaryContent())),StringComparison.OrdinalIgnoreCase)
            || app.Metadata.BaseStream is not MemoryStream metadata
            || !string.Equals(root.GetProperty("metadata_sha256").GetString(),
                Convert.ToHexString(SHA256.HashData(metadata.ToArray())),StringComparison.OrdinalIgnoreCase));

    internal static int Recover(MethodAnalysisContext method,byte[] original,byte[] expected)
    {
        if(Arm64HfaLayout.Fields(method.DeclaringType!)==null)
            return RecoverIntegralLeaf(method,original,expected);
        if(method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.IsStatic
            || method.DeclaringType is not {} owner || Arm64HfaLayout.Fields(owner) is not {} lanes
            || method.ControlFlowGraph is not {} cfg || method.ParameterOperands.FirstOrDefault() is not Register {Name:"X0"} self
            || original.Length is <8 or >128 || original.Length%4!=0 || expected.Length!=original.Length)return 0;
        var native=Disassembler.Disassemble(original,0,new(true,true,false)).ToArray();
        if(native.Length*4!=original.Length || native[^1].Mnemonic!=Arm64Mnemonic.RET)return 0;
        var accesses=new List<(long Offset,int Width,bool Write)>();
        for(var n=0;n<native.Length;n++)
        {
            var instruction=native[n];var before=BitConverter.ToUInt32(original,n*4);var after=BitConverter.ToUInt32(expected,n*4);
            if(instruction.Mnemonic==Arm64Mnemonic.RET)
            {if(n!=native.Length-1 || before!=after)return 0;continue;}
            if(instruction.Mnemonic is not (Arm64Mnemonic.LDR or Arm64Mnemonic.STR or Arm64Mnemonic.LDP or Arm64Mnemonic.STP))
            {
                if(!instruction.Mnemonic.ToString().StartsWith("F",StringComparison.Ordinal) || before!=after
                    || Gpr(instruction.Op0Reg) || Gpr(instruction.Op1Reg) || Gpr(instruction.Op2Reg))return 0;
                continue;
            }
            var width=NewArmV8InstructionSet.StoreWidth(Arm64Mnemonic.STR,instruction.Op0Reg);
            var pair=instruction.Mnemonic is Arm64Mnemonic.LDP or Arm64Mnemonic.STP;
            if(width is not (4 or 8) || !Fp(instruction.Op0Reg)
                || pair && (!Fp(instruction.Op1Reg) || NewArmV8InstructionSet.StoreWidth(Arm64Mnemonic.STR,instruction.Op1Reg)!=width)
                || instruction.MemBase!=Arm64Register.X0 || instruction.MemAddendReg!=Arm64Register.INVALID
                || instruction.MemIndexMode!=Arm64MemoryIndexMode.Offset || instruction.MemOffset<16)return 0;
            var shift=pair?15:10;uint mask=pair?127u:4095u;
            var encoded=(before>>shift)&mask;var signed=pair && (encoded&64)!=0?(long)encoded-128:encoded;
            if(signed*width!=instruction.MemOffset || 16%width!=0)return 0;
            var rewritten=(before&~(mask<<shift))|((uint)((instruction.MemOffset-16)/width)&mask)<<shift;
            if(rewritten!=after)return 0;
            var write=instruction.Mnemonic is Arm64Mnemonic.STR or Arm64Mnemonic.STP;
            for(var k=0;k<(pair?2:1);k++)
            {
                var offset=instruction.MemOffset+k*width;
                if(!lanes.Any(l=>l.Offset==offset-16 && TypeSizes.UnboxedSize(l.FieldType,8)==width))return 0;
                accesses.Add((offset,width,write));
            }
        }
        var size=TypeSizes.UnboxedSize(owner,8);
        if(accesses.Count==0 || !accesses.Any(a=>a.Offset+a.Width>size))return 0;
        var edits=new List<(Instruction Instruction,int Operand,MemoryOperand Memory)>();
        var observed=new List<(long Offset,int Width,bool Write)>();
        foreach(var instruction in cfg.Instructions)
        {
            if(instruction.OpCode==OpCode.Return && method.IsVoid)continue;
            for(var n=0;n<instruction.Operands.Count;n++)
            {
                var operand=instruction.Operands[n];
                if(operand is MemoryOperand memory && Equals(memory.Base,self))
                {
                    if(memory.Index!=null || memory.Scale!=0 || instruction.OpCode!=OpCode.Move || instruction.Operands.Count!=2)return 0;
                    var write=n==0;var width=write?instruction.NativeWriteSize:instruction.NativeReadSize;
                    var access=(memory.Addend,width,write);
                    if(!accesses.Contains(access))return 0;
                    observed.Add(access);edits.Add((instruction,n,memory));
                }
                else if(Uses(operand,self))return 0;
            }
        }
        if(!accesses.OrderBy(a=>a).SequenceEqual(observed.OrderBy(a=>a)))return 0;
        foreach(var edit in edits)
        {var memory=edit.Memory;memory.Addend-=16;edit.Instruction.SetOperand(edit.Operand,memory);}
        return edits.Count;
    }

    private static bool IntegralLeafCandidate(MethodAnalysisContext method)
        => !method.IsStatic && method.Parameters.Count==0
            && method.DeclaringType is {IsValueType:true,IsGenericInstance:false} owner
            && !owner.HasAnyGenericParameters() && IntegralWidth(method.ReturnType)>0;

    private static int IntegralWidth(TypeAnalysisContext type)=>type.FullName switch
    {
        "System.Boolean" or "System.Byte" or "System.SByte"=>1,
        "System.Char" or "System.UInt16" or "System.Int16"=>2,
        "System.UInt32" or "System.Int32"=>4,
        "System.UInt64" or "System.Int64"=>8,
        _=>0
    };

    // ONLY a complete integral field-return leaf. Exact original metadata and
    // native counterpart bytes are checked by Run before entering this routine.
    // An access inside the unboxed size remains ambiguous and is never shifted.
    internal static int RecoverIntegralLeaf(MethodAnalysisContext method,byte[] original,byte[] expected)
    {
        if(!IntegralLeafCandidate(method) || method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.ControlFlowGraph is not {} cfg || original.Length!=8 || expected.Length!=8
            || method.ParameterOperands.FirstOrDefault() is not Register {Name:"X0"} self
            || BitConverter.ToUInt32(original,4)!=0xd65f03c0 || BitConverter.ToUInt32(expected,4)!=0xd65f03c0)return 0;
        var word=BitConverter.ToUInt32(original,0);var counterpart=BitConverter.ToUInt32(expected,0);
        // Unsigned-immediate encodings, destination W0/X0 and receiver X0.
        var opcode=word&0xffc003ffu;
        var width=IntegralWidth(method.ReturnType);
        var correct=method.ReturnType.FullName switch
        {
            "System.Boolean" or "System.Byte"=>opcode==0x39400000u,
            "System.SByte"=>opcode==0x39c00000u,
            "System.Char" or "System.UInt16"=>opcode==0x79400000u,
            "System.Int16"=>opcode==0x79c00000u,
            "System.UInt32" or "System.Int32"=>opcode==0xb9400000u,
            "System.UInt64" or "System.Int64"=>opcode==0xf9400000u,
            _=>false
        };
        if(!correct)return 0;
        var offset=(long)((word>>10)&4095)*width;
        var owner=method.DeclaringType!;var size=TypeSizes.UnboxedSize(owner,8);
        if(offset<16 || size<=0 || offset+width<=size
            || counterpart!=((word&~(4095u<<10))|((uint)((offset-16)/width)<<10)))return 0;
        var fields=owner.Fields.Where(f=>!f.IsStatic && f.Offset==offset-16
            && TrivialConstructorRecovery.SameType(f.FieldType,method.ReturnType)).ToArray();
        if(fields.Length!=1 || fields[0].Offset+width>size)return 0;
        var body=cfg.Instructions.Where(i=>i.OpCode!=OpCode.Nop).ToArray();
        if(body.Length!=2 || body[0] is not {OpCode:OpCode.Move,NativeWriteSize:0,
                Operands:[Register {Name:"X0"},MemoryOperand memory]}
            || body[0].NativeReadSize!=width || !Equals(memory.Base,self)
            || memory.Index!=null || memory.Scale!=0 || memory.Addend!=offset
            || body[1] is not {OpCode:OpCode.Return,Operands:[Register {Name:"X0"}]})return 0;
        memory.Addend-=16;body[0].SetOperand(1,memory);return 1;
    }
    private static bool Fp(Arm64Register r)=>r is >=Arm64Register.S0 and <=Arm64Register.S31 or >=Arm64Register.D0 and <=Arm64Register.D31;
    private static bool Gpr(Arm64Register r)=>r is >=Arm64Register.X0 and <=Arm64Register.X31 or >=Arm64Register.W0 and <=Arm64Register.W31;
    private static bool Uses(IOperand operand,Register self)=>operand switch
    {
        Register r=>r.Equals(self),MemoryOperand m=>m.Base!=null && Uses(m.Base,self) || m.Index!=null && Uses(m.Index,self),
        AddressOf a=>Uses(a.Target,self),_=>false
    };
}
