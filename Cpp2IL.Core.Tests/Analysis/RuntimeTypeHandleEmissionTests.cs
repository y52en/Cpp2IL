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

public class RuntimeTypeHandleEmissionTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void ProvenTypeHandleEmitsTokenNotZeroPointerOrDoubleTypeConversion(bool runtimeClass)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Resolve", t.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var generic = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            GenericParameterAttributes.None, context); context.GenericParameters.Add(generic);
        var handle = app.Assemblies.SelectMany(a => a.Types).Single(x => x.FullName == "System.RuntimeTypeHandle");
        var assembly = new AssemblyDefinition("TypeHandleFixture" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("TypeHandleFixture.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Test", "Generated", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(owner);
        var scope = module.CorLibTypeFactory.CorLibScope;
        var typeSignature = scope.CreateTypeReference("System", "Type").ToTypeSignature(false);
        var method = new MethodDefinition("Resolve", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static, MethodSignature.CreateStatic(typeSignature, 1, []));
        method.GenericParameters.Add(new GenericParameter("T", 0)); owner.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        IOperand operand = runtimeClass ? new RuntimeClassTypeAnalysisContext(generic, t.SystemObjectType.DeclaringAssembly) : generic;
        var emit = typeof(IlGenerator).GetMethod("LoadOperand", BindingFlags.NonPublic | BindingFlags.Static)!;
        emit.Invoke(null, [operand, method, new Dictionary<LocalVariable, CilLocalVariable>(), method, handle]);
        Assert.That(method.CilMethodBody.Instructions.Count(i => i.OpCode == CilOpCodes.Ldtoken), Is.EqualTo(1));
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Call), Is.False,
            "a RuntimeTypeHandle argument must not already be a System.Type");
        var getType = scope.CreateTypeReference("System", "Type").CreateMemberReference("GetTypeFromHandle",
            MethodSignature.CreateStatic(typeSignature, [scope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));
        method.CilMethodBody.Instructions.Add(CilOpCodes.Call, getType);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        using var stream = new MemoryStream(); module.Write(stream);
        // Execute only this newly emitted metadata fixture, never restored game code.
        var generated = Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Resolve")!;
        Assert.That(generated.MakeGenericMethod(typeof(string)).Invoke(null, null), Is.EqualTo(typeof(string)));
        Assert.That(generated.MakeGenericMethod(typeof(int)).Invoke(null, null), Is.EqualTo(typeof(int)));
    }
}
