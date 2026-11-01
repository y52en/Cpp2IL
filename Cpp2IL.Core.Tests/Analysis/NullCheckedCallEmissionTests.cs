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

namespace Cpp2IL.Core.Tests.Analysis;

public class NullCheckedCallEmissionTests
{
    [Test]
    public void ActualEmittedSealedDelegateInvokeCallsTheCallbackAndThrowsOnNull()
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var module=new ModuleDefinition("DelegateNullFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var assembly=new AssemblyDefinition("DelegateNullFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));assembly.Modules.Add(module);
        var callback=new TypeDefinition("Fixture","Callback",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System","MulticastDelegate"));
        module.TopLevelTypes.Add(callback);
        callback.Methods.Add(new MethodDefinition(".ctor",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,[module.CorLibTypeFactory.Object,module.CorLibTypeFactory.IntPtr]))
            {ImplAttributes=AsmResolver.PE.DotNet.Metadata.Tables.MethodImplAttributes.Runtime});
        var invoke=new MethodDefinition("Invoke",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Virtual|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.NewSlot,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,[module.CorLibTypeFactory.Int32]))
            {ImplAttributes=AsmResolver.PE.DotNet.Metadata.Tables.MethodImplAttributes.Runtime};callback.Methods.Add(invoke);
        var callbackContext=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Callback",
            t.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.MulticastDelegate"),TypeAttributes.Public|TypeAttributes.Sealed);
        callbackContext.PutExtraData("AsmResolverType",callback);
        var target=new InjectedMethodAnalysisContext(callbackContext,"Invoke",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Virtual,[t.SystemInt32Type]);target.PutExtraData("AsmResolverMethod",invoke);
        var owner=new TypeDefinition("Fixture","Runner",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var run=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,[callback.ToTypeSignature(false)]));owner.Methods.Add(run);
        run.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var receiver=new LocalVariable("callback",new(null,"X0"),callbackContext);
        var slot=new CilLocalVariable(callback.ToTypeSignature(false));run.CilMethodBody.LocalVariables.Add(slot);
        run.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);run.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,slot);
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Run",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[callbackContext]);
        var operation=new Instruction(0,OpCode.CallVoid,target,receiver,new Immediate(-1)){NativeVirtualDispatch=true};
        typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!.Invoke(null,
            [operation,context,run,new Dictionary<LocalVariable,CilLocalVariable>{{receiver,slot}},run]);
        run.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        Assert.That(run.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Callvirt),Is.True);
        Assert.That(target.IsVirtual,Is.True);Assert.That(operation.NativeNullCheckedCall,Is.False);
        using var stream=new MemoryStream();module.Write(stream);var runtime=Assembly.Load(stream.ToArray());
        var execute=runtime.GetType("Fixture.Runner")!.GetMethod("Run")!;
        var observed=0;Action<int> observer=value=>observed=value;
        var instance=Delegate.CreateDelegate(runtime.GetType("Fixture.Callback")!,observer.Target,observer.Method);
        execute.Invoke(null,[instance]);Assert.That(observed,Is.EqualTo(-1));
        var error=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,[null]));
        Assert.That(error!.InnerException,Is.TypeOf<NullReferenceException>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ActualEmittedNonvirtualCallPreservesNullCheckWithoutChangingTarget(bool checkedCall)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var module=new ModuleDefinition("NullCall"+Guid.NewGuid().ToString("N")+".dll",
            new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var assembly=new AssemblyDefinition(module.Name!,new Version(1,0));assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Receiver",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var target=new MethodDefinition("NoDereference",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32));owner.Methods.Add(target);
        target.CilMethodBody=new CilMethodBody();target.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4,7);
        target.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var managedOwner=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Fixture","Receiver",
            types.SystemObjectType,TypeAttributes.Public);managedOwner.PutExtraData("AsmResolverType",owner);
        var managedTarget=new InjectedMethodAnalysisContext(managedOwner,"NoDereference",types.SystemInt32Type,
            MethodAttributes.Public,[]);managedTarget.PutExtraData("AsmResolverMethod",target);
        var context=new InjectedMethodAnalysisContext(managedOwner,"Run",types.SystemVoidType,MethodAttributes.Static,[managedOwner]);
        var run=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,[owner.ToTypeSignature(false)]));
        owner.Methods.Add(run);run.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var receiver=new LocalVariable("receiver",new(null,"X0"),managedOwner);
        var slot=new CilLocalVariable(owner.ToTypeSignature(false));run.CilMethodBody.LocalVariables.Add(slot);
        run.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);run.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,slot);
        var instruction=new Instruction(0,OpCode.CallVoid,managedTarget,receiver){NativeNullCheckedCall=checkedCall};
        typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!.Invoke(null,
            [instruction,context,run,new Dictionary<LocalVariable,CilLocalVariable>{{receiver,slot}},run]);
        run.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        Assert.That(run.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Callvirt),Is.EqualTo(checkedCall));
        Assert.That(instruction.NativeVirtualDispatch,Is.False);Assert.That(managedTarget.IsVirtual,Is.False);
        using var stream=new MemoryStream();module.Write(stream);
        var runtime=Assembly.Load(stream.ToArray()).GetType("Fixture.Receiver")!;var execute=runtime.GetMethod("Run")!;
        var instance=System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(runtime);
        Assert.DoesNotThrow(()=>execute.Invoke(null,[instance]));
        if(checkedCall)
        {
            var error=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,[null]));
            Assert.That(error!.InnerException,Is.TypeOf<NullReferenceException>());
        }
        else Assert.DoesNotThrow(()=>execute.Invoke(null,[null]),"the fixture target never dereferences this");
    }
}
