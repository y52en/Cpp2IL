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

public class GenericUnboxEmissionTests
{
    [Test]
    public void GenericCheckedConversionPreservesValuesNullsAndInvalidCastExceptions()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Convert",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            System.Reflection.GenericParameterAttributes.None,context);
        context.GenericParameters.Add(parameter);context.OverrideReturnType=parameter;
        var source=new LocalVariable("source",new Register(null,"source"),app.SystemTypes.SystemObjectType);
        var result=new LocalVariable("result",new Register(null,"result"),parameter);
        var assembly=new AssemblyDefinition("UnboxFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("UnboxFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var signature=new GenericParameterSignature(GenericParameterType.Method,0);
        var method=new MethodDefinition("Convert",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(signature,1,[module.CorLibTypeFactory.Object]));
        method.GenericParameters.Add(new GenericParameter("T",0));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var sourceLocal=new CilLocalVariable(module.CorLibTypeFactory.Object);
        var resultLocal=new CilLocalVariable(signature);
        method.CilMethodBody.LocalVariables.Add(sourceLocal);method.CilMethodBody.LocalVariables.Add(resultLocal);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,sourceLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable> {[source]=sourceLocal,[result]=resultLocal};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in new Instruction[]{new(0,OpCode.UnboxAny,result,parameter,source),new(1,OpCode.Return,result)})
            emit.Invoke(null,[instruction,context,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Count(i=>i.OpCode==CilOpCodes.Unbox_Any),Is.EqualTo(1));
        using var stream=new MemoryStream();module.Write(stream);
        // Execute only this newly generated fixture, never the original game DLL.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Convert")!;
        object? Convert(Type t,object? value)=>generated.MakeGenericMethod(t).Invoke(null,[value]);
        var guid=Guid.Parse("12345678-1234-5678-1234-567812345678");
        Assert.That(Convert(typeof(int),37),Is.EqualTo(37));
        Assert.That(Convert(typeof(Guid),guid),Is.EqualTo(guid));
        Assert.That(Convert(typeof(string),"captured"),Is.EqualTo("captured"));
        Assert.That(Convert(typeof(string),null),Is.Null);
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Convert(typeof(int),null))!.InnerException,
            Is.TypeOf<NullReferenceException>());
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Convert(typeof(int),37L))!.InnerException,
            Is.TypeOf<InvalidCastException>());
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Convert(typeof(string),37))!.InnerException,
            Is.TypeOf<InvalidCastException>());
    }
}
