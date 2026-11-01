using System;
using System.Collections.Generic;
using System.Linq;
using System.IO;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64BitfieldExtractTests
{
    private static Arm64Instruction Native(bool wide,bool signed,bool insert,int lsb,int count,int destination=9,int source=8)
    {
        var bits=wide?64:32;var immr=insert?(bits-lsb)%bits:lsb;
        var imms=insert?count-1:lsb+count-1;
        var word=(wide?0x93400000u:0x13000000u)|(signed?0u:0x40000000u)
            |(uint)immr<<16|(uint)imms<<10|(uint)source<<5|(uint)destination;
        return Disassembler.Disassemble(BitConverter.GetBytes(word),0x169b580,new(true,true,false)).Single();
    }

    private static ulong Execute(List<Instruction> instructions,ulong source,int destination=9)
    {
        var registers=Enumerable.Range(0,31).ToDictionary(i=>"X"+i,_=>source);
        ulong Read(IOperand value)=>value switch{Register r=>registers[r.Name],Immediate i=>i.UnsignedValue,_=>throw new Exception()};
        foreach(var instruction in instructions)
        {
            var p=instruction.Operands;
            var result=instruction.OpCode switch {
                OpCode.NumericConvert=>((TypeAnalysisContext)p[1]).FullName switch {
                    "System.UInt32"=>(uint)Read(p[3]),"System.Int32"=>unchecked((ulong)(int)Read(p[3])),
                    _=>Read(p[3])},
                OpCode.And=>Read(p[1])&Read(p[2]),
                OpCode.ShiftLeft=>Read(p[1])<<(int)Read(p[2]),
                OpCode.ShiftRight=>unchecked((ulong)((long)Read(p[1])>>(int)Read(p[2]))),
                OpCode.ShiftRightUnsigned=>Read(p[1])>>(int)Read(p[2]),_=>throw new Exception()};
            registers[((Register)p[0]).Name]=result;
        }
        return destination==31?source:registers["X"+destination];
    }

    [TestCase(false,false,false)] [TestCase(false,false,true)]
    [TestCase(false,true,false)] [TestCase(false,true,true)]
    [TestCase(true,false,false)] [TestCase(true,false,true)]
    [TestCase(true,true,false)] [TestCase(true,true,true)]
    public void AllDecodedBitfieldRangesMatchIndependentBitReference(bool wide,bool signed,bool insert)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;var bits=wide?64:32;var tested=0;
        for(var lsb=0;lsb<bits;lsb++)
        for(var count=1;count<=bits-lsb;count++)
        {
            var native=Native(wide,signed,insert,lsb,count);
            // ARM uses other aliases (ASR/LSR/SXTH/LSL) for some encodings.
            if(native.Mnemonic!=((signed,insert) switch {
                (true,true)=>Arm64Mnemonic.SBFIZ,(true,false)=>Arm64Mnemonic.SBFX,
                (false,true)=>Arm64Mnemonic.UBFIZ,_=>Arm64Mnemonic.UBFX}))continue;
            tested++;
            var lowered=Arm64BitfieldExtractRecovery.Lower(native,types)!;Assert.That(lowered,Is.Not.Null);
            foreach(var source in new[]{0UL,ulong.MaxValue,1UL,0x800000008000ffffUL,0x0123456789abcdefUL})
            {
                ulong expected=0;
                for(var bit=0;bit<bits;bit++)
                {
                    var relative=insert?bit-lsb:bit;
                    if(relative<0)continue;
                    var src=relative<count?(insert?relative:relative+lsb)
                        :signed?(insert?count-1:lsb+count-1):-1;
                    if(src>=0 && (source>>src&1)!=0)expected|=1UL<<bit;
                }
                Assert.That(Execute(lowered,source),Is.EqualTo(expected),native+" source="+source.ToString("x"));
            }
        }
        Assert.That(tested,Is.GreaterThan(bits));
    }

    [TestCase("153c1f13",0xffffUL,0xfffffffeUL)]
    [TestCase("08010013",1UL,0xffffffffUL)]
    public void OriginalSignedCounterexamplesKeepSign(string hex,ulong input,ulong expected)
    {
        var native=Disassembler.Disassemble(Convert.FromHexString(hex),0x169b580,new(true,true,false)).Single();
        var lowered=Arm64BitfieldExtractRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(Execute(lowered,input,(int)native.Op0Reg-(int)Arm64Register.W0),Is.EqualTo(expected));
    }

    [TestCase(false)] [TestCase(true)]
    public void AliasedReceiverReadsBeforeWriting(bool wide)
    {
        var native=Native(wide,true,true,1,16,8,8);
        var lowered=Arm64BitfieldExtractRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes)!;
        Assert.That(Execute(lowered,0xffff,8),Is.EqualTo(wide?ulong.MaxValue-1:0xfffffffeUL));
    }

    [TestCase(0xd503201fu)] [TestCase(0x1e202800u)]
    public void OtherInstructionsRemainUnsupported(uint word)
    {
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        Assert.That(Arm64BitfieldExtractRecovery.Lower(native,TestGameLoader.LoadSimple2019Game().SystemTypes),Is.Null);
    }

    [TestCase(false,false,false)] [TestCase(false,false,true)]
    [TestCase(false,true,false)] [TestCase(false,true,true)]
    [TestCase(true,false,false)] [TestCase(true,false,true)]
    [TestCase(true,true,false)] [TestCase(true,true,true)]
    public void ActualEmittedCilExecutesSignedAndUnsignedBitfields(bool wide,bool signed,bool insert)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var scalar=wide?types.SystemUInt64Type:types.SystemUInt32Type;
        var context=new InjectedMethodAnalysisContext(types.SystemObjectType,"Run",scalar,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("BitfieldFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("BitfieldFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var signature=wide?module.CorLibTypeFactory.UInt64:module.CorLibTypeFactory.UInt32;
        var method=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(signature,[signature]));
        owner.Methods.Add(method);method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var locals=new Dictionary<LocalVariable,CilLocalVariable>();var registers=new Dictionary<string,LocalVariable>();
        LocalVariable Declare(string name,TypeAnalysisContext type)
        {
            var local=new LocalVariable(name,new Register(null,name),type);registers.Add(name,local);
            var cilType=type.FullName switch {
                "System.Int32"=>module.CorLibTypeFactory.Int32,"System.UInt32"=>module.CorLibTypeFactory.UInt32,
                "System.Int64"=>module.CorLibTypeFactory.Int64,_=>module.CorLibTypeFactory.UInt64};
            var slot=new CilLocalVariable(cilType);locals.Add(local,slot);method.CilMethodBody.LocalVariables.Add(slot);return local;
        }
        var input=Declare("X8",scalar);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,locals[input]);
        var lowered=Arm64BitfieldExtractRecovery.Lower(Native(wide,signed,insert,1,16),types)!;
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in lowered)
        {
            var name=((Register)instruction.Operands[0]).Name;
            var type=instruction.OpCode==OpCode.NumericConvert?(TypeAnalysisContext)instruction.Operands[1]
                :registers[((Register)instruction.Operands[1]).Name].Type!;
            Declare(name,type);
            var mapped=instruction.Operands.Select(p=>p is Register r?(IOperand)registers[r.Name]:p).ToList();
            var operation=new Instruction(instruction.Index,instruction.OpCode,mapped){NativeArithmeticSize=wide?8:4};
            emit.Invoke(null,[operation,context,method,locals,method]);
        }
        emit.Invoke(null,[new Instruction(lowered.Count,OpCode.Return,registers["X9"]),context,method,locals,method]);
        using var stream=new MemoryStream();module.Write(stream);
        var run=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Run")!;
        foreach(var bits in new[]{0UL,ulong.MaxValue,0xffffUL,0x800000008000ffffUL})
        {
            var field=insert?bits&0xffff:(bits>>1)&0xffff;
            var expected=signed?unchecked((ulong)(long)(short)field):field;
            if(insert)expected<<=1;
            object value=wide?(object)bits:(uint)bits;
            object result=wide?(object)expected:(uint)expected;
            Assert.That(run.Invoke(null,[value]),Is.EqualTo(result));
        }
    }
}
