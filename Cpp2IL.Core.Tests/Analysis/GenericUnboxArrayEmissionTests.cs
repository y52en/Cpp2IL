using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericUnboxArrayEmissionTests
{
    [Test]
    public void EmittedArrayStorePreservesNullThenCastThenBoundsExceptionOrder()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Set",
            app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var t=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            System.Reflection.GenericParameterAttributes.None,context);context.GenericParameters.Add(t);
        var array=new LocalVariable("array",new Register(null,"array"),new SzArrayTypeAnalysisContext(t));
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var converted=new LocalVariable("converted",new Register(null,"converted"),t);
        var assembly=new AssemblyDefinition("ArrayUnboxFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("ArrayUnboxFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var signature=new GenericParameterSignature(GenericParameterType.Method,0);
        var method=new MethodDefinition("Set",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,1,[new SzArrayTypeSignature(signature),module.CorLibTypeFactory.Object]));
        method.GenericParameters.Add(new GenericParameter("T",0));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var al=new CilLocalVariable(new SzArrayTypeSignature(signature));
        var vl=new CilLocalVariable(module.CorLibTypeFactory.Object);var cl=new CilLocalVariable(signature);
        foreach(var local in new[]{al,vl,cl})method.CilMethodBody.LocalVariables.Add(local);
        var code=method.CilMethodBody.Instructions;
        code.Add(CilOpCodes.Ldarg_0);code.Add(CilOpCodes.Stloc,al);
        code.Add(CilOpCodes.Ldarg_1);code.Add(CilOpCodes.Stloc,vl);
        var store=new CilInstruction(CilOpCodes.Nop);
        void Exception(string name)
        {
            var ctor=module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System",name)
                .CreateMemberReference(".ctor",MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
            code.Add(CilOpCodes.Newobj,ctor);code.Add(CilOpCodes.Throw);
        }
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{array,al},{value,vl},{converted,cl}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[new Instruction(90,OpCode.ArrayNullCheck,array),context,method,locals,method]);
        Assert.That(code[code.Count-2].OpCode,Is.EqualTo(CilOpCodes.Ldlen));
        Assert.That(code[code.Count-1].OpCode,Is.EqualTo(CilOpCodes.Pop));
        emit.Invoke(null,[new Instruction(0,OpCode.UnboxAny,converted,t,value),context,method,locals,method]);
        code.Add(CilOpCodes.Ldloc,al);code.Add(CilOpCodes.Ldlen);code.Add(CilOpCodes.Conv_I4);
        code.Add(CilOpCodes.Brtrue,new CilInstructionLabel(store));Exception("IndexOutOfRangeException");code.Add(store);
        emit.Invoke(null,[new Instruction(1,OpCode.Move,new ArrayAccess(array,new Immediate(0)),converted),context,method,locals,method]);
        code.Add(CilOpCodes.Ret);
        using var stream=new MemoryStream();module.Write(stream);
        // Never load or execute any original game DLL. Only this new fixture.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Set")!;
        void Set(Type type,object? array,object? value)=>generated.MakeGenericMethod(type).Invoke(null,[array,value]);
        var ints=new[]{11};Set(typeof(int),ints,37);Assert.That(ints[0],Is.EqualTo(37));
        var guid=Guid.Parse("12345678-1234-5678-1234-567812345678");var guids=new Guid[1];
        Set(typeof(Guid),guids,guid);Assert.That(guids[0],Is.EqualTo(guid));
        var strings=new string[1];Set(typeof(string),strings,"value");Assert.That(strings[0],Is.EqualTo("value"));
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Set(typeof(int),null,37L))!.InnerException,Is.TypeOf<NullReferenceException>());
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Set(typeof(int),Array.Empty<int>(),37L))!.InnerException,Is.TypeOf<InvalidCastException>());
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Set(typeof(int),Array.Empty<int>(),37))!.InnerException,Is.TypeOf<IndexOutOfRangeException>());
        Assert.That(Assert.Throws<TargetInvocationException>(()=>Set(typeof(int),ints,null))!.InnerException,Is.TypeOf<NullReferenceException>());
        Assert.That(ints[0],Is.EqualTo(37));
    }
}
