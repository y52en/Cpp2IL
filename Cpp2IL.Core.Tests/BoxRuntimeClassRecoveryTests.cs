using System.Collections.Generic;
using System.Linq;
using System;
using System.IO;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using LibCpp2IL.BinaryStructures;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class BoxRuntimeClassRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    static void Recover(Instruction call, params LocalVariable[] locals)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var method = new InjectedMethodAnalysisContext(types.SystemObjectType,"BoxCaller",types.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,[]);
        method.ControlFlowGraph = new ISILControlFlowGraph([call,new(1,OpCode.Return)]);
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        method.AnalysisWarnings = [];
        KeyFunctionRecovery.Run(method);
    }

    [TestCase(false,false)]
    [TestCase(true,false)]
    [TestCase(false,true)]
    [TestCase(true,true)]
    public void BoxesRepresentedTypeNotMetadataPointer(bool localHandle,bool referenceType)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var type = referenceType ? types.SystemObjectType : types.SystemInt32Type;
        var handle = new RuntimeClassTypeAnalysisContext(type,type.DeclaringAssembly);
        var handleLocal = new LocalVariable("klass",new Register(null,"klass"),handle);
        var storage = new LocalVariable("storage",new Register(null,"storage"),type);
        var result = new LocalVariable("boxed",new Register(null,"boxed"),types.SystemObjectType);
        var address = new AddressOf(storage);
        var call = new Instruction(0,OpCode.Call,new StringLiteral("il2cpp_value_box"),result,
            localHandle ? handleLocal : handle,address);
        Recover(call,handleLocal,storage,result);
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Box));
        Assert.That(call.Operands[1],Is.SameAs(type));
        Assert.That(call.Operands[2],Is.SameAs(address));
        Assert.That(storage.Type,Is.SameAs(type));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void UnknownClassOrUnknownHelperRemainsDiagnostic(bool unknownHelper)
    {
        var handle = new LocalVariable("klass",new Register(null,"klass"));
        var result = new LocalVariable("boxed",new Register(null,"boxed"));
        var call = new Instruction(0,OpCode.Call,
            new StringLiteral(unknownHelper ? "unclassified_helper" : "il2cpp_value_box"),result,handle,new Immediate(0));
        Recover(call,handle,result);
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Call));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void BoxingStorageTypingIsMonotonic(bool conflicting)
    {
        var types=Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var original=conflicting ? types.SystemObjectType : null;
        var storage=new LocalVariable("storage",new Register(null,"storage"),original);
        var result=new LocalVariable("boxed",new Register(null,"boxed"),types.SystemObjectType);
        var method=new InjectedMethodAnalysisContext(types.SystemObjectType,"Caller",types.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new ISILControlFlowGraph([
            new(0,OpCode.Box,result,types.SystemInt32Type,new AddressOf(storage)),new(1,OpCode.Return)]);
        Assert.That(LocalVariables.TypeAddressedLocals(method),Is.EqualTo(!conflicting));
        Assert.That(storage.Type,Is.SameAs(original ?? types.SystemInt32Type));
        Assert.That(LocalVariables.TypeAddressedLocals(method),Is.False);
    }

    [Test]
    public void OpenGenericBoxingUsesTypedStorageAndExecutesForValueAndReferenceArguments()
    {
        var types=Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var context=new InjectedMethodAnalysisContext(types.SystemObjectType,"BoxDefault",types.SystemObjectType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            System.Reflection.GenericParameterAttributes.None,context);
        context.GenericParameters.Add(parameter);
        var storage=new LocalVariable("value",new Register(null,"value"));
        var result=new LocalVariable("boxed",new Register(null,"boxed"),types.SystemObjectType);
        var box=new Instruction(0,OpCode.Box,result,parameter,new AddressOf(storage));
        context.ControlFlowGraph=new ISILControlFlowGraph([box,new(1,OpCode.Return,result)]);
        Assert.That(LocalVariables.TypeAddressedLocals(context),Is.True);
        Assert.That(storage.Type,Is.SameAs(parameter));

        var assembly=new AssemblyDefinition("BoxFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("BoxFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method=new MethodDefinition("BoxDefault",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Object,1,[]));
        method.GenericParameters.Add(new GenericParameter("T",0));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var valueLocal=new CilLocalVariable(new GenericParameterSignature(GenericParameterType.Method,0));
        var objectLocal=new CilLocalVariable(module.CorLibTypeFactory.Object);
        method.CilMethodBody.LocalVariables.Add(valueLocal);method.CilMethodBody.LocalVariables.Add(objectLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable> {[storage]=valueLocal,[result]=objectLocal};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[box,context,method,locals,method]);
        emit.Invoke(null,[new Instruction(1,OpCode.Return,result),context,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Single(i=>i.OpCode==CilOpCodes.Box).Operand!.ToString(),Does.Contain("!!0"));
        using var stream=new MemoryStream();module.Write(stream);
        // Execute only the freshly generated fixture, never any game assembly.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("BoxDefault")!;
        Assert.That(generated.MakeGenericMethod(typeof(string)).Invoke(null,null),Is.Null);
        Assert.That(generated.MakeGenericMethod(typeof(int)).Invoke(null,null),Is.EqualTo(0));
        Assert.That(generated.MakeGenericMethod(typeof(Guid)).Invoke(null,null),Is.EqualTo(Guid.Empty));
    }
}
