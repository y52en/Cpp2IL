using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeNumericConversionTests
{
    [TestCase(Arm64Mnemonic.FCVTZS,Arm64Register.W0,Arm64Register.S0,"System.Int32","System.Single")]
    [TestCase(Arm64Mnemonic.FCVTZS,Arm64Register.X0,Arm64Register.D0,"System.Int64","System.Double")]
    [TestCase(Arm64Mnemonic.FCVTZU,Arm64Register.W0,Arm64Register.D0,"System.UInt32","System.Double")]
    [TestCase(Arm64Mnemonic.FCVTZU,Arm64Register.X0,Arm64Register.S0,"System.UInt64","System.Single")]
    [TestCase(Arm64Mnemonic.SCVTF,Arm64Register.S0,Arm64Register.W0,"System.Single","System.Int32")]
    [TestCase(Arm64Mnemonic.SCVTF,Arm64Register.D0,Arm64Register.X0,"System.Double","System.Int64")]
    [TestCase(Arm64Mnemonic.UCVTF,Arm64Register.S0,Arm64Register.X0,"System.Single","System.UInt64")]
    [TestCase(Arm64Mnemonic.UCVTF,Arm64Register.D0,Arm64Register.W0,"System.Double","System.UInt32")]
    [TestCase(Arm64Mnemonic.FCVT,Arm64Register.D0,Arm64Register.S0,"System.Double","System.Single")]
    [TestCase(Arm64Mnemonic.FCVT,Arm64Register.S0,Arm64Register.D0,"System.Single","System.Double")]
    [TestCase(Arm64Mnemonic.SCVTF,Arm64Register.S0,Arm64Register.S0,"System.Single","System.Int32")]
    [TestCase(Arm64Mnemonic.UCVTF,Arm64Register.D0,Arm64Register.D0,"System.Double","System.UInt64")]
    [TestCase(Arm64Mnemonic.FCVTZS,Arm64Register.S0,Arm64Register.S0,"System.Int32","System.Single")]
    [TestCase(Arm64Mnemonic.FCVTZU,Arm64Register.D0,Arm64Register.D0,"System.UInt64","System.Double")]
    public void ContractRetainsDirectionWidthAndSignedness(Arm64Mnemonic mnemonic,Arm64Register target,Arm64Register source,string targetType,string sourceType)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var contract=NativeNumericConversion.Contract(app.SystemTypes,mnemonic,target,source);
        Assert.That(contract?.Target.FullName,Is.EqualTo(targetType));
        Assert.That(contract?.Source.FullName,Is.EqualTo(sourceType));
    }

    [TestCase(Arm64Mnemonic.FCVTNS,Arm64Register.W0,Arm64Register.S0)]
    [TestCase(Arm64Mnemonic.FCVTMS,Arm64Register.X0,Arm64Register.D0)]
    [TestCase(Arm64Mnemonic.FCVT,Arm64Register.S0,Arm64Register.S0)]
    [TestCase(Arm64Mnemonic.SCVTF,Arm64Register.V0,Arm64Register.X0)]
    public void UnsupportedRoundingAndRegistersAreNotGuessed(Arm64Mnemonic mnemonic,Arm64Register target,Arm64Register source)
        => Assert.That(NativeNumericConversion.Contract(TestGameLoader.LoadSimple2019Game().SystemTypes,mnemonic,target,source),Is.Null);

    [TestCase(0x1e380000u)] // FCVTZS W0,S0
    [TestCase(0x9e380000u)] // FCVTZS X0,S0
    [TestCase(0x1e390000u)] // FCVTZU W0,S0
    [TestCase(0x1e220000u)] // SCVTF S0,W0
    [TestCase(0x1e230000u)] // UCVTF S0,W0
    [TestCase(0x1e22c000u)] // FCVT D0,S0
    [TestCase(0x5e21d800u)] // SCVTF S0,S0, scalar SIMD integer payload
    [TestCase(0x7e21d800u)] // UCVTF S0,S0, scalar SIMD unsigned payload
    public void ActualInstructionLiftIsNotAPlainMove(uint encoding)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Conversion",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(BitConverter.GetBytes(encoding),0x1000,new(true,true,false)).Single();
        var emitted=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!.SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),new object[]{native,emitted,new List<ulong>(),method});
        Assert.That(emitted.Single().OpCode,Is.EqualTo(OpCode.NumericConvert));
        Assert.That(emitted.Single().SourcesAndConstants.Count,Is.EqualTo(1));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void PropagationKeepsConversionAndIlContainsExplicitConv(bool unsignedToFloat)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var sourceType=unsignedToFloat?types.SystemUInt64Type:types.SystemSingleType;
        var targetType=unsignedToFloat?types.SystemSingleType:types.SystemInt32Type;
        var source=new LocalVariable("source",new Register(null,"source"),sourceType);
        var destination=new LocalVariable("destination",new Register(null,"destination"));
        var conversion=new Instruction(0,OpCode.NumericConvert,destination,targetType,sourceType,source);
        var context=new InjectedMethodAnalysisContext(types.SystemObjectType,"Convert",targetType,MethodAttributes.Public|MethodAttributes.Static,[]);
        context.ControlFlowGraph=new([conversion,new(1,OpCode.Return,destination)]);
        context.Locals=[source,destination];context.ParameterLocals=[];context.AnalysisWarnings=[];
        LocalVariables.ResolveTypesAndFields(context);SsaSimplifier.Run(context);
        Assert.That(destination.Type,Is.SameAs(targetType));
        Assert.That(conversion.OpCode,Is.EqualTo(OpCode.NumericConvert));
        var module=new ModuleDefinition("Test.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var corlib=new ModuleDefinition("mscorlib.dll");
        foreach(var type in new[]{sourceType,targetType}.Distinct())
        {
            var definition=new TypeDefinition("System",type.FullName.Split('.').Last(),AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public);
            corlib.TopLevelTypes.Add(definition);type.PutExtraData("AsmResolverType",definition);
        }
        var owner=new TypeDefinition("Test","Conversions",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public);module.TopLevelTypes.Add(owner);
        var method=new MethodDefinition("Convert",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(targetType.ToTypeSignature()));
        owner.Methods.Add(method);IlGenerator.GenerateIl(context,method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i=>i.OpCode==(unsignedToFloat?CilOpCodes.Conv_R4:CilOpCodes.Conv_I4)),Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Conv_R_Un),Is.EqualTo(unsignedToFloat));
    }
}
