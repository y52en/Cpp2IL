using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeAbsoluteTests
{
    [TestCase("unknown-width")]
    [TestCase("source-width")]
    [TestCase("destination-width")]
    [TestCase("recursive-runtime-intrinsic")]
    public void UnsupportedTypesOrRuntimeSelfCallsFailBeforeEmittingAnyIl(string shape)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var ownerContext=shape=="recursive-runtime-intrinsic"?
            new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"System","Math",t.SystemObjectType,
                System.Reflection.TypeAttributes.Public):t.SystemObjectType;
        var context=new InjectedMethodAnalysisContext(ownerContext,shape=="recursive-runtime-intrinsic"?"Abs":"Run",
            t.SystemSingleType,System.Reflection.MethodAttributes.Static,[]);
        var module=new ModuleDefinition("InvalidAbs.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var method=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Single));owner.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody();
        var input=new LocalVariable("input",new Register(null,"V0"),shape=="source-width"?t.SystemDoubleType:t.SystemSingleType);
        var output=new LocalVariable("output",new Register(null,"V1"),shape=="destination-width"?t.SystemDoubleType:t.SystemSingleType);
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        var error=Assert.Throws<TargetInvocationException>(()=>emit.Invoke(null,[
            new Instruction(0,OpCode.Absolute,output,input){NativeFloatingPointSize=shape=="unknown-width"?0:4},
            context,method,new Dictionary<LocalVariable,CilLocalVariable>(),method]));
        Assert.That(error!.InnerException,Is.TypeOf<DecompilerException>());
        Assert.That(method.CilMethodBody.Instructions,Is.Empty);
    }

    [TestCase(0x1e20c000u,4)]
    [TestCase(0x1e20c3ffu,4)]
    [TestCase(0x1e60c000u,8)]
    [TestCase(0x1e60c0e3u,8)]
    public void NativeScalarFabsRetainsPrecisionAndPureUnaryOperands(uint word,int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Fixture",
            app.SystemTypes.SystemVoidType,System.Reflection.MethodAttributes.Static,[]);
        var instruction=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        Assert.That(instruction.Mnemonic,Is.EqualTo(Arm64Mnemonic.FABS));
        Assert.That(NewArmV8InstructionSet.ScalarFloatingPointWidth(instruction,OpCode.Absolute),Is.EqualTo(width));
        var emitted=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),[instruction,emitted,new List<ulong>(),context]);
        var absolute=emitted.Single(i=>i.OpCode==OpCode.Absolute);
        Assert.That(absolute.NativeFloatingPointSize,Is.EqualTo(width));
        Assert.That(absolute.Destination,Is.EqualTo(absolute.Operands[0]));
        Assert.That(absolute.Sources.Count,Is.EqualTo(1));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ActualEmittedCilClearsOnlySignIncludingNegativeZeroAndNanPayload(bool wide)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;var scalar=wide?t.SystemDoubleType:t.SystemSingleType;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Absolute",scalar,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("AbsFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("AbsFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var signature=wide?module.CorLibTypeFactory.Double:module.CorLibTypeFactory.Single;
        var method=new MethodDefinition("Absolute",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(signature,[signature]));
        owner.Methods.Add(method);method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var input=new LocalVariable("input",new Register(null,"V0"),scalar);
        var output=new LocalVariable("output",new Register(null,"V1"),scalar);
        var inputSlot=new CilLocalVariable(signature);var outputSlot=new CilLocalVariable(signature);
        method.CilMethodBody.LocalVariables.Add(inputSlot);method.CilMethodBody.LocalVariables.Add(outputSlot);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,inputSlot);
        var slots=new Dictionary<LocalVariable,CilLocalVariable>{{input,inputSlot},{output,outputSlot}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[new Instruction(0,OpCode.Absolute,output,input){NativeFloatingPointSize=wide?8:4},context,method,slots,method]);
        emit.Invoke(null,[new Instruction(1,OpCode.Return,output),context,method,slots,method]);
        using var stream=new MemoryStream();module.Write(stream);
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Absolute")!;
        ulong[] bits=wide?[0,0x8000000000000000,0xbff0000000000000,0xfff0000000000000,0xfff8123456789abc,0xfff0123456789abc,1,0x8000000000000001]:
            [0,0x80000000,0xbf800000,0xff800000,0xffc12345,0xffa12345,1,0x80000001];
        foreach(var value in bits)
        {
            object argument=wide?(object)BitConverter.Int64BitsToDouble(unchecked((long)value)):
                BitConverter.Int32BitsToSingle(unchecked((int)value));
            var result=generated.Invoke(null,[argument]);
            var observed=wide?unchecked((ulong)BitConverter.DoubleToInt64Bits((double)result!)):
                unchecked((uint)BitConverter.SingleToInt32Bits((float)result!));
            Assert.That(observed,Is.EqualTo(value&(wide?0x7fffffffffffffffUL:0x7fffffffUL)),"input bits "+value.ToString("X"));
        }
    }
}
