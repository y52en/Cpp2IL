using AsmResolver.PE.DotNet.Cil;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IntegralStackConversionTests
{
    [TestCase("Int64","Int32","i4")]
    [TestCase("UInt64","UInt32","u4")]
    [TestCase("UInt64","Byte","u1")]
    [TestCase("Int64","SByte","i1")]
    [TestCase("Int64","Int16","i2")]
    [TestCase("UInt64","UInt16","u2")]
    [TestCase("UInt64","Char","u2")]
    [TestCase("UInt32","Int64","u8")]
    [TestCase("UInt32","UInt64","u8")]
    [TestCase("Byte","Int64","u8")]
    [TestCase("UInt16","Int64","u8")]
    [TestCase("Char","Int64","u8")]
    [TestCase("Int32","UInt64","i8")]
    [TestCase("Int32","Int64","i8")]
    [TestCase("SByte","UInt64","i8")]
    [TestCase("Int16","Int64","i8")]
    public void MetadataPrimitiveWidthAndSourceSignednessDetermineConversion(string source,string target,string name)
    {
        var assembly=TestGameLoader.LoadSimple2019Game().SystemTypes.SystemObjectType.DeclaringAssembly;
        var type=assembly.GetTypeByFullName("System."+source)!;
        var value=new LocalVariable("value",new Register(null,"X0"),type);
        var expected=assembly.GetTypeByFullName("System."+target);
        var conversion=IlGenerator.IntegralLoadConversion(value,expected);
        Assert.That(conversion?.ToString(),Is.EqualTo("conv."+name));
        Assert.That(value.Type,Is.SameAs(type));
    }

    [TestCase("Int32","UInt32")]
    [TestCase("Byte","Int32")]
    [TestCase("Int64","UInt64")]
    [TestCase("Object","Int32")]
    [TestCase("String","Int64")]
    [TestCase("IntPtr","Int64")]
    [TestCase("UIntPtr","Int64")]
    [TestCase("Boolean","Int64")]
    [TestCase("Int64","Boolean")]
    [TestCase("Single","Int64")]
    [TestCase("Int64","Double")]
    [TestCase(null,"Int64")]
    [TestCase("Int64",null)]
    public void SameStackWidthOrUnprovedNonintegerContractsAreNeverCoerced(string? source,string? target)
    {
        var assembly=TestGameLoader.LoadSimple2019Game().SystemTypes.SystemObjectType.DeclaringAssembly;
        var value=new LocalVariable("value",new Register(null,"X0"),source==null?null:assembly.GetTypeByFullName("System."+source));
        Assert.That(IlGenerator.IntegralLoadConversion(value,target==null?null:assembly.GetTypeByFullName("System."+target)),Is.Null);
        Assert.That(IlGenerator.IntegralLoadConversion(new Immediate(0),assembly.GetTypeByFullName("System.Int64")),Is.Null);
    }

    [TestCase("Int64","Int32","Int64")]
    [TestCase("Int32","UInt64","UInt64")]
    [TestCase("UInt32","Int64","Int64")]
    [TestCase("Int32","Int32",null)]
    [TestCase("Object","Int64",null)]
    public void MixedWidthComparisonWidensBothSidesToOneStackWidthWithoutTruncatingTheIndex(string left,string right,string? result)
    {
        var assembly=TestGameLoader.LoadSimple2019Game().SystemTypes.SystemObjectType.DeclaringAssembly;
        LocalVariable Local(string name,string type)=>new(name,new Register(null,name),assembly.GetTypeByFullName("System."+type));
        var instruction=new Instruction(0,OpCode.CheckLess,Local("condition","Boolean"),Local("left",left),Local("right",right));
        Assert.That(IlGenerator.ComparisonStackType(instruction)?.FullName,Is.EqualTo(result==null?null:"System."+result));
    }

    [TestCase("UInt64","Int32")]
    [TestCase("UInt64","UInt32")]
    [TestCase("UInt32","Int64")]
    [TestCase("Int32","Int64")]
    [TestCase("Int32","UInt64")]
    public void ActualEmittedReturnConversionExecutesWithTruncationOrCorrectSignExtension(string from,string to)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var sourceType=t.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System."+from)!;
        var targetType=t.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System."+to)!;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Convert",targetType,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("IntegerStackFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("IntegerStackFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        TypeSignature Signature(string name)=>name switch
        {
            "Int32"=>module.CorLibTypeFactory.Int32,"UInt32"=>module.CorLibTypeFactory.UInt32,
            "Int64"=>module.CorLibTypeFactory.Int64,"UInt64"=>module.CorLibTypeFactory.UInt64,
            _=>throw new ArgumentException(),
        };
        var method=new MethodDefinition("Convert",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(Signature(to),[Signature(from)]));owner.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var operand=new LocalVariable("input",new Register(null,"X0"),sourceType);
        var local=new CilLocalVariable(Signature(from));method.CilMethodBody.LocalVariables.Add(local);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,local);
        typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!
            .Invoke(null,[new Instruction(0,OpCode.Return,operand),context,method,
                new Dictionary<LocalVariable,CilLocalVariable>{{operand,local}},method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==IlGenerator.IntegralLoadConversion(operand,targetType)),Is.True);
        using var bytes=new MemoryStream();module.Write(bytes);
        var generated=Assembly.Load(bytes.ToArray()).GetType("Fixture.Generated")!.GetMethod("Convert")!;
        object value=from switch {"UInt64"=>0x1ffffffffUL,"UInt32"=>(object)uint.MaxValue,_=>-1};
        object expected=to switch {"UInt32"=>(object)uint.MaxValue,"Int32"=>-1,
            "UInt64"=>(object)ulong.MaxValue,_=>from=="UInt32"?(long)uint.MaxValue:-1L};
        Assert.That(generated.Invoke(null,[value]),Is.EqualTo(expected));
    }
}
