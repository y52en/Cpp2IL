using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void VirtualMethodDirectCallAndNativeDispatchRemainDistinct(bool nativeDispatch)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Dispatch",app.SystemTypes.SystemObjectType,System.Reflection.TypeAttributes.Public);
        var target=owner.InjectMethodContext("Target",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Virtual,[]);
        var caller=new InjectedMethodAnalysisContext(owner,"Caller",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        var receiver=new LocalVariable("receiver",new Register(null,"X0"),owner);
        var call=new Instruction(0,OpCode.CallVoid,target,receiver,new Immediate(0)){NativeVirtualDispatch=nativeDispatch};
        caller.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        caller.Locals=[receiver];caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        var module=new ModuleDefinition("Dispatch.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var type=new TypeDefinition("Test","Dispatch",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);owner.PutExtraData("AsmResolverType",type);
        var targetDef=new MethodDefinition("Target",MethodAttributes.Public|MethodAttributes.Virtual,MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        type.Methods.Add(targetDef);target.PutExtraData("AsmResolverMethod",targetDef);
        var callerDef=new MethodDefinition("Caller",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(callerDef);IlGenerator.GenerateIl(caller,callerDef);
        var actual=callerDef.CilMethodBody!.Instructions.Single(i=>i.Operand is IMethodDescriptor m && m.Name=="Target");
        Assert.That(actual.OpCode,Is.EqualTo(nativeDispatch?CilOpCodes.Callvirt:CilOpCodes.Call));
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void ProvenDefaultStructEmitsInitobjInsteadOfIntegerZero()
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var context=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Data",app.SystemTypes.SystemValueTypeType,System.Reflection.TypeAttributes.Public);
        var caller=new InjectedMethodAnalysisContext(context,"Caller",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        var local=new LocalVariable("data",new Register(null,"stack_-80"),context);
        caller.ControlFlowGraph=new([new(0,OpCode.Move,local,new DefaultStructValue(context)),new(1,OpCode.Return)]);
        caller.Locals=[local];caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        var module=new ModuleDefinition("Test.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var type=new TypeDefinition("Test","Data",TypeAttributes.Public|TypeAttributes.SequentialLayout,
            new TypeReference(module,module.CorLibTypeFactory.CorLibScope,"System","ValueType"));
        module.TopLevelTypes.Add(type);context.PutExtraData("AsmResolverType",type);
        var method=new MethodDefinition("Caller",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);IlGenerator.GenerateIl(caller,method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i=>i.OpCode==CilOpCodes.Initobj),Is.True);
        Assert.That(method.CilMethodBody!.Instructions.Any(i=>i.OpCode==CilOpCodes.Ldc_I4_0),Is.False);
    }

    [Test]
    public void NestedStructStoreAddressesParentFieldBeforeStoringScalar()
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var assembly=app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var holder=new InjectedTypeAnalysisContext(assembly,"Test","Holder",app.SystemTypes.SystemObjectType,System.Reflection.TypeAttributes.Public);
        var data=new InjectedTypeAnalysisContext(assembly,"Test","Data",app.SystemTypes.SystemValueTypeType,System.Reflection.TypeAttributes.Public);
        var parent=holder.InjectFieldContext("Data",data,System.Reflection.FieldAttributes.Public);
        var scalar=data.InjectFieldContext("X",app.SystemTypes.SystemSingleType,System.Reflection.FieldAttributes.Public);
        var local=new LocalVariable("holder",new Register(null,"X19"),holder);
        var field=new FieldReference(scalar,local,16){Parent=new FieldReference(parent,local,16)};
        var caller=new InjectedMethodAnalysisContext(holder,"Write",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        caller.ControlFlowGraph=new([new(0,OpCode.Move,field,new FloatLiteral(1)),new(1,OpCode.Return)]);
        caller.Locals=[local];caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        var module=new ModuleDefinition("Test.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var dataDef=new TypeDefinition("Test","Data",TypeAttributes.Public|TypeAttributes.SequentialLayout,
            new TypeReference(module,module.CorLibTypeFactory.CorLibScope,"System","ValueType"));
        var holderDef=new TypeDefinition("Test","Holder",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(dataDef);module.TopLevelTypes.Add(holderDef);
        data.PutExtraData("AsmResolverType",dataDef);holder.PutExtraData("AsmResolverType",holderDef);
        var parentDef=new FieldDefinition("Data",FieldAttributes.Public,new FieldSignature(dataDef.ToTypeSignature()));holderDef.Fields.Add(parentDef);
        var scalarDef=new FieldDefinition("X",FieldAttributes.Public,new FieldSignature(module.CorLibTypeFactory.Single));dataDef.Fields.Add(scalarDef);
        parent.PutExtraData("AsmResolverField",parentDef);scalar.PutExtraData("AsmResolverField",scalarDef);
        var method=new MethodDefinition("Write",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));holderDef.Methods.Add(method);
        IlGenerator.GenerateIl(caller,method);
        var instructions=method.CilMethodBody!.Instructions;
        Assert.That(instructions.Any(i=>i.OpCode==CilOpCodes.Ldflda && i.Operand==parentDef),Is.True);
        Assert.That(instructions.Any(i=>i.OpCode==CilOpCodes.Stfld && i.Operand==scalarDef),Is.True);
        Assert.That(instructions.Any(i=>i.OpCode==CilOpCodes.Stfld && i.Operand==parentDef),Is.False);
    }

    [Test]
    public void StaticCall_DoesNotLoadMethodInfoOperand()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;
        var systemInt = appContext.SystemTypes.SystemInt32Type;

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var targetContext = new InjectedMethodAnalysisContext(
            systemObject,
            "TargetStatic",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [systemInt, systemInt]);

        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));

        var instructions = new List<Instruction>
        {
            
            new(0, OpCode.Move, x, Imm(5)),
            new(1, OpCode.Move, y, Imm(10)),
            // Operand layout: target, arg0, arg1, trailing-non-parameter.
            new(2, OpCode.CallVoid, targetContext, x, y, Imm(999)),
            new(3, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        callerContext.Locals = [x, y];
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        var targetMethodDef = new MethodDefinition("TargetStatic", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32]));
        typeDef.Methods.Add(targetMethodDef);
        targetContext.PutExtraData("AsmResolverMethod", targetMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        var il = callerMethodDef.CilMethodBody!.Instructions;

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True, "expected generated method to contain a call");
        Assert.That(il.Any(i => i.Operand is int intOperand && intOperand == 999), Is.False,
            "trailing non-parameter operand must not be emitted as a call argument");
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc), Is.EqualTo(2),
            "expected exactly two Ldloc instructions for the two parameters of the target method");
    }
}
