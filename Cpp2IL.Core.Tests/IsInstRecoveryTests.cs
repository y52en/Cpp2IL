using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.Utils;
using Disarm;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class IsInstRecoveryTests
{
    [Test]
    public void NativeAnchor_DoesNotReadCallsFromNextFunction()
    {
        // BL +4; RET; BL +8. Only the first call belongs to the anchor.
        byte[] bytes = [1, 0, 0, 0x94, 0xC0, 3, 0x5F, 0xD6, 2, 0, 0, 0x94];
        var instructions = Disassembler.Disassemble(bytes, 0x1000, new(true, true, false)).ToList();
        Assert.That(NewArm64KeyFunctionAddresses.FindIsInstAnchorCall(instructions), Is.EqualTo(0x1004UL));
    }

    [Test]
    public void NativeAnchor_WithConditionalControlFlow_IsNotGuessed()
    {
        // BL +4; CBZ X0,+4; RET.
        byte[] bytes = [1, 0, 0, 0x94, 0x20, 0, 0, 0xB4, 0xC0, 3, 0x5F, 0xD6];
        var instructions = Disassembler.Disassemble(bytes, 0x1000, new(true, true, false)).ToList();
        Assert.That(NewArm64KeyFunctionAddresses.FindIsInstAnchorCall(instructions), Is.Zero);
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static InjectedMethodAnalysisContext Context(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var context = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        context.Locals = locals.ToList();
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        return context;
    }

    [TestCase(false, false)]
    [TestCase(true, false)]
    [TestCase(false, true)]
    [TestCase(true, true)]
    public void KnownType_RewritesAsObjectOrNull_NotBoolean(bool classLocal, bool valueType)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        var testedType = valueType ? types.SystemInt32Type : types.SystemObjectType;
        var source = new LocalVariable("source", new Register(null, "source"), types.SystemObjectType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var handle = new LocalVariable("klass", new Register(null, "klass"),
            new RuntimeClassTypeAnalysisContext(testedType, testedType.DeclaringAssembly));
        var call = new Instruction(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result,
            source, classLocal ? handle : testedType);
        var context = Context([call, new(1, OpCode.Return)], source, result, handle);
        KeyFunctionRecovery.Run(context);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.IsInst));
        Assert.That(call.Operands[1], Is.SameAs(testedType));
        Assert.That(call.Destination, Is.SameAs(result));
        Assert.That(call.Sources.Single(), Is.SameAs(source));
        Assert.That(result.Type, Is.SameAs(valueType ? types.SystemObjectType : testedType));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void UnresolvedClassOrUnknownHelper_RemainsDiagnostic(bool unknownHelper)
    {
        var source = new LocalVariable("source", new Register(null, "source"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var handle = new LocalVariable("klass", new Register(null, "klass"));
        var call = new Instruction(0, OpCode.Call, new StringLiteral(unknownHelper ? "unclassified_helper" : "il2cpp_vm_object_is_inst"), result,
            source, unknownHelper ? Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType : handle);
        KeyFunctionRecovery.Run(Context([call, new(1, OpCode.Return)], source, result, handle));
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void EmitsIsinst_WithoutCastclassOrNewobj(bool nullInput)
    {
        var testedType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemObjectType;
        var source = new LocalVariable("source", new Register(null, "source"), testedType);
        var result = new LocalVariable("result", new Register(null, "result"), testedType);
        var context = Context([new(0, OpCode.IsInst, result, testedType,
            nullInput ? new Immediate(0) : source), new(1, OpCode.Return)], source, result);
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var corlib = new ModuleDefinition("mscorlib.dll");
        var definition = new TypeDefinition("System", "Object", TypeAttributes.Public);
        corlib.TopLevelTypes.Add(definition);
        testedType.PutExtraData("AsmResolverType", definition);
        var type = new TypeDefinition("Cpp2IL.Core.Tests", "IsInst", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Count(i => i.OpCode == CilOpCodes.Isinst), Is.EqualTo(1));
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Castclass || i.OpCode == CilOpCodes.Newobj), Is.False);
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.EqualTo(nullInput));
    }
}
