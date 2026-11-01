using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeIndirectValueArgumentTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _value = null!;
    [OneTimeSetUp]
    public void Load()
    {
        _app = TestGameLoader.LoadSimple2019Game();
        _value = _app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Keyframe");
    }

    private (MethodAnalysisContext Caller, MethodAnalysisContext Target, Instruction Call, LocalVariable Value, LocalVariable Receiver, Instruction Guard) Fixture(bool returns = false, bool instance = false)
    {
        var owner = _app.SystemTypes.SystemObjectType;
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", _app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var target = new InjectedMethodAnalysisContext(owner, "Target", returns ? _app.SystemTypes.SystemInt32Type : _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static), [_value]);
        var value = new LocalVariable("storage", new(null, "not-a-stack-name"), _value);
        var receiver = new LocalVariable("receiver", new(null, "X0"), owner);
        caller.Locals.AddRange([value, receiver]);
        var operands = new System.Collections.Generic.List<IOperand> { target };
        if (returns) operands.Add(new LocalVariable("result", new(null, "result"), _app.SystemTypes.SystemInt32Type));
        if (instance) operands.Add(receiver);
        operands.Add(new AddressOf(value));
        var call = new Instruction(1, returns ? OpCode.Call : OpCode.CallVoid, operands);
        var guard = new Instruction(0, OpCode.CallVoid, new Immediate(777));
        caller.ControlFlowGraph = new([guard, call, new(2, OpCode.Return)]);
        return (caller, target, call, value, receiver, guard);
    }

    [TestCase(false, false)] [TestCase(false, true)] [TestCase(true, false)] [TestCase(true, true)]
    public void ExactByValueParameterUsesTheValueAndPreservesReceiverAndEffects(bool returns, bool instance)
    {
        var f = Fixture(returns, instance);
        var before = f.Call.Operands.ToArray();
        Assert.That(NativeIndirectValueArgumentRecovery.IsIndirectAggregate(_value), Is.True);
        Assert.That(NativeIndirectValueArgumentRecovery.Rewrite(f.Caller, f.Call, true), Is.EqualTo(1));
        Assert.That(f.Call.Operands[^1], Is.SameAs(f.Value));
        Assert.That(f.Call.Operands.Take(before.Length - 1), Is.EqualTo(before.Take(before.Length - 1)));
        Assert.That(f.Value.Type, Is.SameAs(_value));
        Assert.That(f.Caller.ControlFlowGraph!.Instructions.Contains(f.Guard), Is.True);
        Assert.That(NativeIndirectValueArgumentRecovery.Rewrite(f.Caller, f.Call, true), Is.Zero);
    }

    [TestCase("unreviewed")] [TestCase("unknown-storage")] [TestCase("wrong-storage-type")]
    [TestCase("foreign-local")] [TestCase("this-storage")] [TestCase("method-info")]
    [TestCase("return-buffer")] [TestCase("byref-parameter")] [TestCase("scalar-parameter")]
    [TestCase("small-struct")] [TestCase("floating-hfa")] [TestCase("all-floating")]
    [TestCase("unknown-callee")] [TestCase("missing-argument")] [TestCase("non-call")]
    [TestCase("duplicate-call")] [TestCase("foreign-call")] [TestCase("non-local-address")]
    public void NoUntypedRetaggingOrPointerGuessing(string shape)
    {
        var f = Fixture();
        var block = f.Caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(f.Call));
        var reviewed = true;
        switch (shape)
        {
            case "unreviewed": reviewed = false; break;
            case "unknown-storage": f.Value.Type = null; break;
            case "wrong-storage-type": f.Value.Type = _app.SystemTypes.SystemInt32Type; break;
            case "foreign-local": f.Caller.Locals.Remove(f.Value); break;
            case "this-storage": f.Value.IsThis = true; break;
            case "method-info": f.Value.IsMethodInfo = true; break;
            case "return-buffer": f.Value.IsReturnBuffer = true; break;
            case "byref-parameter": f.Target.Parameters[0].ParameterType = new ByRefTypeAnalysisContext(_value); break;
            case "scalar-parameter": f.Value.Type = f.Target.Parameters[0].ParameterType = _app.SystemTypes.SystemInt32Type; break;
            case "small-struct": f.Value.Type = f.Target.Parameters[0].ParameterType = _app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Guid"); break;
            case "floating-hfa": f.Value.Type = f.Target.Parameters[0].ParameterType = _app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Quaternion"); break;
            case "all-floating": f.Value.Type = f.Target.Parameters[0].ParameterType = _app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Matrix4x4"); break;
            case "unknown-callee": f.Call.SetOperand(0, new Immediate(123)); break;
            case "missing-argument": f.Call.SetOperands(f.Target); break;
            case "non-call": f.Call.OpCode = OpCode.Move; break;
            case "duplicate-call": block.Instructions.Add(f.Call); break;
            case "foreign-call": block.Instructions.Remove(f.Call); break;
            case "non-local-address": f.Call.SetOperand(1, new AddressOf(new MemoryOperand(f.Receiver))); break;
        }
        var operands = f.Call.Operands.ToArray(); var type = f.Value.Type;
        Assert.That(NativeIndirectValueArgumentRecovery.Rewrite(f.Caller, f.Call, reviewed), Is.Zero);
        Assert.That(f.Call.Operands, Is.EqualTo(operands));
        Assert.That(f.Value.Type, Is.SameAs(type));
    }

    [Test]
    public void ValueLoadUsesLdlocInsteadOfLdloca()
    {
        var f = Fixture();
        Assert.That(NativeIndirectValueArgumentRecovery.Rewrite(f.Caller, f.Call, true), Is.EqualTo(1));
        var module = new ModuleDefinition("ValueArgument.dll");
        var method = new MethodDefinition("Load", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        method.CilMethodBody = new CilMethodBody();
        var local = new CilLocalVariable(module.CorLibTypeFactory.Int32);
        method.CilMethodBody.LocalVariables.Add(local);
        var locals = new System.Collections.Generic.Dictionary<LocalVariable, CilLocalVariable> { [f.Value] = local };
        var load = typeof(IlGenerator).GetMethod("LoadOperand", BindingFlags.NonPublic | BindingFlags.Static)!;
        load.Invoke(null, [f.Call.Operands[^1], method, locals, method, _value]);
        Assert.That(method.CilMethodBody.Instructions.Select(i => i.OpCode), Is.EqualTo(new[] { CilOpCodes.Ldloc }));
    }

    [Test]
    public void ProductionDeclinesTheUnrelatedTestImage()
    {
        var f = Fixture();
        Assert.That(NativeIndirectValueArgumentRecovery.Run(f.Caller), Is.Zero);
        Assert.That(f.Call.Operands[^1], Is.TypeOf<AddressOf>());
    }
}
