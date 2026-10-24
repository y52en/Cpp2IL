using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericByRefEmissionTests
{
    [Test]
    public void GenericManagedPointerCopyUsesLdobjStobjAndExecutesForBothInstantiationKinds()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Copy",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            System.Reflection.GenericParameterAttributes.None,context);
        context.GenericParameters.Add(parameter);context.OverrideReturnType=parameter;
        var source=new LocalVariable("source",new Register(null,"source"),parameter);
        var pointer=new LocalVariable("pointer",new Register(null,"pointer"),new ByRefTypeAnalysisContext(parameter));
        var read=new LocalVariable("read",new Register(null,"read"),parameter);
        var assembly=new AssemblyDefinition("ByRefFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("ByRefFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var signature=new GenericParameterSignature(GenericParameterType.Method,0);
        var method=new MethodDefinition("Copy",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(signature,1,[signature]));
        method.GenericParameters.Add(new GenericParameter("T",0));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var sourceLocal=new CilLocalVariable(signature);var targetLocal=new CilLocalVariable(signature);
        var pointerLocal=new CilLocalVariable(new ByReferenceTypeSignature(signature));var readLocal=new CilLocalVariable(signature);
        foreach(var local in new[]{sourceLocal,targetLocal,pointerLocal,readLocal})method.CilMethodBody.LocalVariables.Add(local);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,sourceLocal);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldloca,targetLocal);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,pointerLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable> {[source]=sourceLocal,[pointer]=pointerLocal,[read]=readLocal};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in new Instruction[]{
            new(0,OpCode.Move,new MemoryOperand(pointer),source),
            new(1,OpCode.Move,read,new MemoryOperand(pointer)),new(2,OpCode.Return,read)})
            emit.Invoke(null,[instruction,context,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Count(i=>i.OpCode==CilOpCodes.Stobj),Is.EqualTo(1));
        Assert.That(method.CilMethodBody.Instructions.Count(i=>i.OpCode==CilOpCodes.Ldobj),Is.EqualTo(1));
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Stind_Ref||i.OpCode==CilOpCodes.Ldind_Ref),Is.False);
        using var stream=new MemoryStream();module.Write(stream);
        // Execute only this newly generated fixture; original game DLLs are metadata inputs only.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Copy")!;
        var guid=Guid.Parse("12345678-1234-5678-1234-567812345678");
        Assert.That(generated.MakeGenericMethod(typeof(string)).Invoke(null,["captured"]),Is.EqualTo("captured"));
        Assert.That(generated.MakeGenericMethod(typeof(int)).Invoke(null,[37]),Is.EqualTo(37));
        Assert.That(generated.MakeGenericMethod(typeof(Guid)).Invoke(null,[guid]),Is.EqualTo(guid));
    }
}
