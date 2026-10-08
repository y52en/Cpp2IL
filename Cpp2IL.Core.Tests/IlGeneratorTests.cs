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
