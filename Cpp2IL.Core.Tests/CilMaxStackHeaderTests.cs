using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;

namespace Cpp2IL.Core.Tests;

public class CilMaxStackHeaderTests
{
    private static CilMethodBody Body(bool returnsInt = false)
    {
        var module = new ModuleDefinition("DetachedMaxStackControl");
        var method = new MethodDefinition("M", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnsInt ? module.CorLibTypeFactory.Int32 : module.CorLibTypeFactory.Void));
        var body = new CilMethodBody { MaxStack = 0, ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        return body;
    }

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(16)]
    [TestCase(512)]
    public void BalancedBodyGetsExactHeaderWithoutChangingInstructions(int depth)
    {
        var body = Body();
        for (var n = 0; n < depth; n++) body.Instructions.Add(CilOpCodes.Ldc_I4_1);
        for (var n = 0; n < depth; n++) body.Instructions.Add(CilOpCodes.Pop);
        body.Instructions.Add(CilOpCodes.Ret);
        var before = body.Instructions.ToArray();
        Assert.That(IlGenerator.TryFinalizeMaxStack(body), Is.True);
        Assert.That(body.MaxStack, Is.EqualTo(depth));
        Assert.That(body.Instructions.ToArray(), Is.EqualTo(before));
        Assert.That(body.ComputeMaxStackOnBuild, Is.False);
    }

    [Test]
    public void MutuallyExclusiveBranchesDoNotAccumulateStackDepth()
    {
        var body = Body(true);
        var alternative = new CilInstruction(CilOpCodes.Ldc_I4_2);
        var ret = new CilInstruction(CilOpCodes.Ret);
        body.Instructions.Add(CilOpCodes.Ldc_I4_0);
        body.Instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel(alternative));
        body.Instructions.Add(CilOpCodes.Ldc_I4_1);
        body.Instructions.Add(CilOpCodes.Br, new CilInstructionLabel(ret));
        body.Instructions.Add(alternative); body.Instructions.Add(ret);
        Assert.That(IlGenerator.TryFinalizeMaxStack(body), Is.True);
        Assert.That(body.MaxStack, Is.EqualTo(1));
    }

    [Test]
    public void UnderflowIsNotReclassifiedAsValidOrGivenAReplacementHeader()
    {
        var body = Body(); body.MaxStack = 77;
        body.Instructions.Add(CilOpCodes.Pop); body.Instructions.Add(CilOpCodes.Ret);
        Assert.That(IlGenerator.TryFinalizeMaxStack(body), Is.False);
        Assert.That(body.MaxStack, Is.EqualTo(77));
    }

    [Test]
    public void CallSignatureDeterminesStackConsumption()
    {
        var body = Body(); var module = new ModuleDefinition("DetachedCallControl");
        var target = new MethodDefinition("Two", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                new TypeSignature[] { module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32 }));
        body.Instructions.Add(CilOpCodes.Ldc_I4_0); body.Instructions.Add(CilOpCodes.Ldc_I4_1);
        body.Instructions.Add(CilOpCodes.Call, target); body.Instructions.Add(CilOpCodes.Ret);
        Assert.That(IlGenerator.TryFinalizeMaxStack(body), Is.True);
        Assert.That(body.MaxStack, Is.EqualTo(2));
    }
}
