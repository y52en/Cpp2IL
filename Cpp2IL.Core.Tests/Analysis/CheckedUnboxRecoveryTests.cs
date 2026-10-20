using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Collections.Generic;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;
using AType = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AMethod = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using AField = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class CheckedUnboxRecoveryTests
{
    private static Instruction Call(ApplicationAnalysisContext app, IOperand handle)
        => new(0, OpCode.Call, new Immediate(0xA61E70), new LocalVariable("address", new Register(null,"X0")),
            new LocalVariable("boxed", new Register(null,"X1"), app.SystemTypes.SystemObjectType), handle, new Immediate(123));

    [TestCase(false)]
    [TestCase(true)]
    public void KnownTypeProducesManagedByrefAndDropsOnlyRawArgumentPadding(bool typedLocal)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemInt32Type;
        var klass=new RuntimeClassTypeAnalysisContext(type,type.DeclaringAssembly);
        var call=Call(app,typedLocal?new LocalVariable("klass",new Register(null,"X2"),klass):klass);
        var result=call.Destination!;
        var boxed=call.Operands[2];
        Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.True);
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Unbox));
        Assert.That(call.Operands.Count,Is.EqualTo(3));
        Assert.That(call.Destination,Is.SameAs(result));
        Assert.That(call.Sources,Is.EquivalentTo(new[]{boxed}));
        Assert.That(((ByRefTypeAnalysisContext)((LocalVariable)result).Type!).ElementType,Is.SameAs(type));
        Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.False);
    }

    [TestCase("reference")]
    [TestCase("unknown")]
    [TestCase("nullable")]
    [TestCase("open")]
    [TestCase("result")]
    [TestCase("value")]
    [TestCase("void")]
    public void UnsupportedContractsAreNotGuessed(string reason)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        IOperand handle=app.SystemTypes.SystemInt32Type;
        if(reason=="reference")handle=app.SystemTypes.SystemStringType;
        if(reason=="unknown")handle=new LocalVariable("runtimeType",new Register(null,"X2"));
        if(reason=="nullable")handle=new GenericInstanceTypeAnalysisContext(app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Nullable`1"),[app.SystemTypes.SystemInt32Type]);
        if(reason=="open")
        {
            var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Open",app.SystemTypes.SystemValueTypeType,System.Reflection.TypeAttributes.Public);
            owner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner));
            handle=owner;
        }
        var call=Call(app,handle);
        if(reason=="result")((LocalVariable)call.Operands[1]).Type=app.SystemTypes.SystemIntPtrType;
        if(reason=="value")((LocalVariable)call.Operands[2]).Type=app.SystemTypes.SystemSingleType;
        if(reason=="void")call.OpCode=OpCode.CallVoid;
        var opcode=call.OpCode;var count=call.Operands.Count;
        Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.False);
        Assert.That(call.OpCode,Is.EqualTo(opcode));Assert.That(call.Operands.Count,Is.EqualTo(count));
    }

    [Test]
    public void SameAddressInAnotherImageDoesNotAuthorizeTheRewrite()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var call=Call(app,app.SystemTypes.SystemInt32Type);
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Read",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        Assert.That(CheckedUnboxRecovery.Run(method),Is.False);
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void ScalarByrefReadUsesTheValueRatherThanPrivateRuntimeBackingFields()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var unbox=Call(app,app.SystemTypes.SystemInt32Type);
        Assert.That(CheckedUnboxRecovery.Rewrite(unbox),Is.True);
        var address=(LocalVariable)unbox.Operands[0];
        var result=new LocalVariable("result",new Register(null,"W1"));
        var load=new Instruction(1,OpCode.Move,result,new MemoryOperand(address)){NativeReadSize=4};
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Read",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([unbox,load,new(2,OpCode.Return)]);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(load.Operands[1],Is.TypeOf<MemoryOperand>());
        Assert.That(result.Type,Is.SameAs(app.SystemTypes.SystemInt32Type));
    }

    [Test]
    public void OrdinaryRefOutParametersKeepTheirExistingTypeInference()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var address=new LocalVariable("ordinaryRef",new Register(null,"X0"),new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var result=new LocalVariable("result",new Register(null,"W1"));
        var load=new Instruction(0,OpCode.Move,result,new MemoryOperand(address)){NativeReadSize=4};
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Read",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([load,new(1,OpCode.Return)]);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(load.Operands[1],Is.TypeOf<FieldReference>());
        Assert.That(result.Type,Is.SameAs(app.SystemTypes.SystemInt32Type));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void UnusedResultDoesNotEliminateCheckedUnboxing(bool nullInput)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var call=Call(app,app.SystemTypes.SystemInt32Type);
        if(nullInput)call.SetOperand(2,new Immediate(0));
        Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.True);
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Check",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        DeadCodeEliminator.Run(method);
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Unbox),"null/type validation remains observable even when unused");
    }

    [TestCase(1)]
    [TestCase(2)]
    [TestCase(8)]
    public void PartialScalarByrefLoadCannotBeEmittedAsAWholeInt32(int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var address=new LocalVariable("address",new Register(null,"X0"),new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var result=new LocalVariable("result",new Register(null,"W1"),app.SystemTypes.SystemInt32Type);
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Read",app.SystemTypes.SystemInt32Type,MethodAttributes.Public|MethodAttributes.Static,[]);
        var module=new ModuleDefinition("Partial.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var type=new TypeDefinition("Test","Generated",AType.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var method=new MethodDefinition("Read",AMethod.Public|AMethod.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody();
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        var error=Assert.Throws<TargetInvocationException>(()=>emit.Invoke(null,[new Instruction(0,OpCode.Move,result,new MemoryOperand(address)){NativeReadSize=width},context,method,new Dictionary<LocalVariable,CilLocalVariable>(),method]));
        Assert.That(error!.InnerException,Is.TypeOf<DecompilerException>());
        Assert.That(error.InnerException!.Message,Does.Contain("partial managed-byref"));
    }

    [Test]
    public void EmittedPrimitiveUnboxChecksNullAndTypeEvenWhenResultIsUnused()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var call=Call(app,app.SystemTypes.SystemInt32Type);Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.True);
        var result=(LocalVariable)call.Operands[0];
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Check",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("PrimitiveUnbox"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("PrimitiveUnbox.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var type=new TypeDefinition("Test","Generated",AType.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var method=new MethodDefinition("Check",AMethod.Public|AMethod.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,[module.CorLibTypeFactory.Object]));type.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"boxed",0));method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var address=new CilLocalVariable(new ByReferenceTypeSignature(module.CorLibTypeFactory.Int32));method.CilMethodBody.LocalVariables.Add(address);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{result,address}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[call,context,method,locals,method]);emit.Invoke(null,[new Instruction(1,OpCode.Return),context,method,locals,method]);
        using var stream=new MemoryStream();module.Write(stream);
        var execute=System.Reflection.Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Check")!;
        Assert.DoesNotThrow(()=>execute.Invoke(null,[123]));
        Assert.DoesNotThrow(()=>execute.Invoke(null,[DayOfWeek.Friday]),"native element-class equality permits matching enum storage");
        var nullError=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,new object?[]{null}));
        Assert.That(nullError!.InnerException,Is.TypeOf<NullReferenceException>());
        var typeError=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,[1.5f]));
        Assert.That(typeError!.InnerException,Is.TypeOf<InvalidCastException>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ActualEmittedUnboxPreservesBoxedStorageAndThrowsOnInvalidInputs(bool store)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var field=vector.Fields.Single(f=>f.Name=="x");
        var call=Call(app,vector);Assert.That(CheckedUnboxRecovery.Rewrite(call),Is.True);
        var address=(LocalVariable)call.Operands[0];
        var boxed=(LocalVariable)call.Operands[2];
        var result=new LocalVariable("result",new Register(null,"S0"),app.SystemTypes.SystemSingleType);
        var access=store?new Instruction(1,OpCode.Move,new FieldReference(field,address,0),new FloatLiteral(99))
            :new Instruction(1,OpCode.Move,result,new FieldReference(field,address,0));
        var ret=store?new Instruction(2,OpCode.Return):new Instruction(2,OpCode.Return,result);
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Access",store?app.SystemTypes.SystemVoidType:app.SystemTypes.SystemSingleType,MethodAttributes.Public|MethodAttributes.Static,[]);
        context.ControlFlowGraph=new([call,access,ret]);context.Locals=[boxed,address,result];
        var assembly=new AssemblyDefinition("CheckedUnbox"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("CheckedUnbox.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var data=new TypeDefinition("Test","Vector",AType.Public|AType.SequentialLayout,new TypeReference(module,module.CorLibTypeFactory.CorLibScope,"System","ValueType"));
        module.TopLevelTypes.Add(data);vector.PutExtraData("AsmResolverType",data);
        foreach(var f in vector.Fields.Where(f=>!f.IsStatic))
        {
            var d=new FieldDefinition(f.Name,AField.Public,new FieldSignature(module.CorLibTypeFactory.Single));data.Fields.Add(d);f.PutExtraData("AsmResolverField",d);
        }
        var generated=new TypeDefinition("Test","Generated",AType.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(generated);
        var method=new MethodDefinition("Access",AMethod.Public|AMethod.Static,MethodSignature.CreateStatic(store?module.CorLibTypeFactory.Void:module.CorLibTypeFactory.Single,[module.CorLibTypeFactory.Object]));generated.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"boxed",0));method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var addrLocal=new CilLocalVariable(new ByReferenceTypeSignature(data.ToTypeSignature()));var valueLocal=new CilLocalVariable(module.CorLibTypeFactory.Single);
        method.CilMethodBody.LocalVariables.Add(addrLocal);method.CilMethodBody.LocalVariables.Add(valueLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{address,addrLocal},{result,valueLocal}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var i in context.ControlFlowGraph.Instructions)emit.Invoke(null,[i,context,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Unbox),Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Unbox_Any),Is.False,"a copy would lose writes to the original box");
        using var stream=new MemoryStream();module.Write(stream);
        // Execute only this newly generated fixture; never execute game DLLs.
        var loaded=System.Reflection.Assembly.Load(stream.ToArray());var runtimeType=loaded.GetType("Test.Vector")!;
        var value=Activator.CreateInstance(runtimeType)!;runtimeType.GetField("x")!.SetValue(value,11f);runtimeType.GetField("y")!.SetValue(value,22f);
        var execute=loaded.GetType("Test.Generated")!.GetMethod("Access")!;
        if(store)execute.Invoke(null,[value]);else Assert.That(execute.Invoke(null,[value]),Is.EqualTo(11f));
        Assert.That(runtimeType.GetField("x")!.GetValue(value),Is.EqualTo(store?99f:11f));Assert.That(runtimeType.GetField("y")!.GetValue(value),Is.EqualTo(22f));
        var nullError=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,new object?[]{null}));
        Assert.That(nullError!.InnerException,Is.TypeOf<NullReferenceException>());
        var typeError=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,["wrong type"]));
        Assert.That(typeError!.InnerException,Is.TypeOf<InvalidCastException>());
    }
}
