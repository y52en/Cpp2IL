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
using AsmMethodAttributes=AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using AsmTypeAttributes=AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericDefaultValueEmissionTests
{
    [Test]
    public void OpenGenericDefaultUsesInitobjAndExecutesCorrectlyForReferenceAndValueArguments()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Default",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            System.Reflection.GenericParameterAttributes.None,context);
        context.GenericParameters.Add(parameter);context.OverrideReturnType=parameter;
        var assembly=new AssemblyDefinition("GenericDefault"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("GenericDefault.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new TypeDefinition("Test","Generated",AsmTypeAttributes.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method=new MethodDefinition("Default",AsmMethodAttributes.Public|AsmMethodAttributes.Static,
            MethodSignature.CreateStatic(new GenericParameterSignature(GenericParameterType.Method,0),1,[]));
        method.GenericParameters.Add(new GenericParameter("T",0));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var instruction=new Instruction(0,OpCode.Return,new DefaultStructValue(parameter));
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[instruction,context,method,new Dictionary<LocalVariable,CilLocalVariable>(),method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Initobj),Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Ldnull),Is.False);
        using var stream=new MemoryStream();module.Write(stream);
        // Execute only this newly generated fixture, never game assemblies.
        var generated=System.Reflection.Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Default")!;
        Assert.That(generated.MakeGenericMethod(typeof(string)).Invoke(null,null),Is.Null);
        Assert.That(generated.MakeGenericMethod(typeof(int)).Invoke(null,null),Is.EqualTo(0));
        Assert.That(generated.MakeGenericMethod(typeof(Guid)).Invoke(null,null),Is.EqualTo(Guid.Empty));
    }
}
