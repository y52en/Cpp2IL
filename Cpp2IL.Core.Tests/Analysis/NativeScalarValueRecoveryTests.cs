using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using AType = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AField = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using AMethod = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeScalarValueRecoveryTests
{
    private sealed class Getter(TypeAnalysisContext owner, string name)
        : InjectedMethodAnalysisContext(owner, name, owner.AppContext.SystemTypes.SystemInt64Type,
            MethodAttributes.Public | MethodAttributes.SpecialName, [])
    { public override ulong UnderlyingPointer => 0x1000; }

    private static (InjectedTypeAnalysisContext Type, FieldAnalysisContext Field, Getter Getter) Fixture()
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Word",
            t.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var field = owner.InjectFieldContext("Payload", t.SystemUInt64Type, FieldAttributes.Private); field.Offset = 0;
        var getter = new Getter(owner, "get_Ticks"); owner.Methods.Add(getter);
        owner.InjectPropertyContext("Ticks", t.SystemInt64Type, getter, null, PropertyAttributes.None);
        return (owner, field, getter);
    }

    [TestCase("exact", true)]
    [TestCase("wrong-mask", false)]
    [TestCase("modified-load", false)]
    [TestCase("modified-and", false)]
    [TestCase("modified-return", false)]
    [TestCase("truncated", false)]
    [TestCase("trailing-code", false)]
    [TestCase("non-original-field", false)]
    [TestCase("two-fields", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("narrow-field", false)]
    [TestCase("private-getter", false)]
    [TestCase("virtual-getter", false)]
    [TestCase("synchronized-getter", false)]
    [TestCase("missing-property", false)]
    [TestCase("two-properties", false)]
    public void OnlyCompleteOriginalMaskedGetterWithMatchingMetadataIsAccepted(string shape, bool expected)
    {
        var f = Fixture();
        var bytes = Convert.FromHexString("080840F900F54092C0035FD6");
        if (shape == "modified-load") bytes[0] ^= 1;
        if (shape == "modified-and") bytes[4] ^= 1;
        if (shape == "modified-return") bytes[8] ^= 1;
        if (shape == "truncated") bytes = bytes[..8];
        if (shape == "trailing-code") bytes = bytes.Concat(new byte[4]).ToArray();
        if (shape == "two-fields") f.Type.InjectFieldContext("Other", f.Field.FieldType, FieldAttributes.Private).Offset = 8;
        if (shape == "wrong-offset") f.Field.Offset = 8;
        if (shape == "narrow-field") f.Field.FieldType = f.Type.AppContext.SystemTypes.SystemInt32Type;
        if (shape == "private-getter") f.Getter.Attributes = MethodAttributes.Private;
        if (shape == "virtual-getter") f.Getter.Attributes |= MethodAttributes.Virtual;
        if (shape == "synchronized-getter") f.Getter.ImplAttributes |= MethodImplAttributes.Synchronized;
        if (shape == "missing-property") f.Type.Properties.Clear();
        if (shape == "two-properties") f.Type.InjectPropertyContext("OtherTicks", f.Getter.ReturnType, f.Getter, null, PropertyAttributes.None);
        Assert.That(NativeScalarValueRecovery.ProveMaskedGetter(f.Getter, f.Field,
            shape == "wrong-mask" ? -1 : NativeScalarValueRecovery.TicksMask, bytes, shape != "non-original-field") != null, Is.EqualTo(expected));
    }

    [TestCase("exact", true)]
    [TestCase("commuted", true)]
    [TestCase("narrow", false)]
    [TestCase("unknown-width", false)]
    [TestCase("floating", false)]
    [TestCase("missing-getter", false)]
    [TestCase("non-scalar-result", false)]
    [TestCase("multiple-definitions", false)]
    public void ProjectionPreservesTheStructAndRejectsUnprovedResultStorage(string shape, bool expected)
    {
        var f = Fixture(); var t = f.Type.AppContext.SystemTypes;
        var source = new LocalVariable("source", new(null, "source"), f.Type);
        var destination = new LocalVariable("masked", new(null, "masked"), shape == "non-scalar-result" ? f.Type : null);
        IOperand[] values = shape == "commuted" ? [new Immediate(NativeScalarValueRecovery.TicksMask), source]
            : [source, new Immediate(NativeScalarValueRecovery.TicksMask)];
        var operation = new Instruction(0, OpCode.And, destination, values[0], values[1])
        { NativeArithmeticSize = shape == "narrow" ? 4 : shape == "unknown-width" ? 0 : 8, NativeFloatingPointSize = shape == "floating" ? 8 : 0 };
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Run", t.SystemInt64Type, MethodAttributes.Public | MethodAttributes.Static, [])
            { ControlFlowGraph = new([operation, new(1, OpCode.Return, destination)]), Locals = [source, destination], ParameterLocals = [source] };
        if (shape == "multiple-definitions") method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(operation)).Instructions.Insert(0,
            new(-1, OpCode.Move, destination, new Immediate(0)));
        Assert.That(NativeScalarValueRecovery.Recover(method, (_, _) => shape == "missing-getter" ? null : f.Getter, _ => null), Is.EqualTo(expected ? 1 : 0));
        Assert.That(source.Type, Is.SameAs(f.Type), "Other consumers retain the original struct");
        Assert.That(operation.OpCode, Is.EqualTo(expected ? OpCode.Call : OpCode.And));
        if (expected) Assert.That(((AddressOf)operation.Operands[2]).Target, Is.SameAs(source));
    }

    [Test]
    public void GeneratedCilMasksFlagsAndSubtractsSignedPayloadWithoutInvalidStructArithmetic()
    {
        var f = Fixture(); var t = f.Type.AppContext.SystemTypes;
        var rawGetter = new Getter(f.Type, "get_Raw");
        var assembly = new AssemblyDefinition("ScalarProjection" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("ScalarProjection.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var data = new TypeDefinition("Fixture", "Word", AType.Public | AType.Sealed | AType.SequentialLayout,
            new TypeReference(module, module.CorLibTypeFactory.CorLibScope, "System", "ValueType"));
        var owner = new TypeDefinition("Fixture", "Generated", AType.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(data); module.TopLevelTypes.Add(owner);
        f.Type.PutExtraData("AsmResolverType", data);
        var payload = new FieldDefinition("Payload", AField.Public, new FieldSignature(module.CorLibTypeFactory.UInt64)); data.Fields.Add(payload);
        void BindGetter(Getter context, bool masked)
        {
            var defined = new MethodDefinition(context.Name, AMethod.Public, MethodSignature.CreateInstance(module.CorLibTypeFactory.Int64));
            data.Methods.Add(defined); context.PutExtraData("AsmResolverMethod", defined);
            defined.CilMethodBody = new CilMethodBody();
            defined.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            defined.CilMethodBody.Instructions.Add(CilOpCodes.Ldfld, payload);
            if (masked) { defined.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I8, NativeScalarValueRecovery.TicksMask); defined.CilMethodBody.Instructions.Add(CilOpCodes.And); }
            defined.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        }
        BindGetter(f.Getter, true); BindGetter(rawGetter, false);
        var date = new LocalVariable("date", new(null, "date"), f.Type);
        var offset = new LocalVariable("offset", new(null, "offset"), f.Type);
        var ticks = new LocalVariable("ticks", new(null, "ticks"));
        var result = new LocalVariable("result", new(null, "result"), t.SystemInt64Type);
        var context = new InjectedMethodAnalysisContext(t.SystemObjectType, "Calculate", t.SystemInt64Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [date, offset, ticks, result], ParameterLocals = [date, offset],
            ControlFlowGraph = new([new(0, OpCode.And, ticks, date, new Immediate(NativeScalarValueRecovery.TicksMask)) { NativeArithmeticSize = 8 },
                new(1, OpCode.Subtract, result, ticks, offset) { NativeArithmeticSize = 8 }, new(2, OpCode.Return, result)])
        };
        Assert.That(NativeScalarValueRecovery.Recover(context, (_, _) => f.Getter, _ => rawGetter), Is.EqualTo(2));
        var method = new MethodDefinition("Calculate", AMethod.Public | AMethod.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int64, [data.ToTypeSignature(true), data.ToTypeSignature(true)]));
        owner.Methods.Add(method); method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var locals = new Dictionary<LocalVariable, CilLocalVariable>();
        foreach (var local in context.Locals)
        {
            var storage = new CilLocalVariable(ReferenceEquals(local.Type, f.Type) ? data.ToTypeSignature(true) : module.CorLibTypeFactory.Int64);
            locals.Add(local, storage); method.CilMethodBody.LocalVariables.Add(storage);
        }
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0); method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, locals[date]);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1); method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, locals[offset]);
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var instruction in context.ControlFlowGraph.Instructions) emit.Invoke(null, [instruction, context, method, locals, method]);

        // Execute an aliasing counterexample: read Value, overwrite Value, then
        // consume the snapshot. A getter moved to the consumer would return 0.
        var holderContext = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Holder",
            t.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var valueContext = holderContext.InjectFieldContext("Value", f.Type, FieldAttributes.Public); valueContext.Offset = 0;
        var holderDefinition = new TypeDefinition("Fixture", "Holder", AType.Public | AType.Sealed | AType.SequentialLayout,
            new TypeReference(module, module.CorLibTypeFactory.CorLibScope, "System", "ValueType"));
        module.TopLevelTypes.Add(holderDefinition); holderContext.PutExtraData("AsmResolverType", holderDefinition);
        var valueDefinition = new FieldDefinition("Value", AField.Public, new FieldSignature(data.ToTypeSignature(true)));
        holderDefinition.Fields.Add(valueDefinition); valueContext.PutExtraData("AsmResolverField", valueDefinition);
        var holderLocal = new LocalVariable("holder", new(null, "holder"), new ByRefTypeAnalysisContext(holderContext));
        var saved = new LocalVariable("saved", new(null, "saved"), f.Type);
        var projected = new LocalVariable("projected", new(null, "projected"), t.SystemInt64Type);
        var fieldAccess = new FieldReference(valueContext, holderLocal, 0);
        var read = new Instruction(0, OpCode.Move, saved, fieldAccess) { NativeReadSize = 8 };
        var overwrite = new Instruction(1, OpCode.Move, fieldAccess, new DefaultStructValue(f.Type));
        var consume = new Instruction(2, OpCode.And, projected, saved, new Immediate(NativeScalarValueRecovery.TicksMask))
            { NativeArithmeticSize = 8 };
        var snapshot = new InjectedMethodAnalysisContext(t.SystemObjectType, "Snapshot", t.SystemInt64Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [holderLocal, saved, projected], ParameterLocals = [holderLocal],
            ControlFlowGraph = new([read, overwrite, consume, new(3, OpCode.Return, projected)])
        };
        Assert.That(NativeScalarValueRecovery.Recover(snapshot, (_, _) => f.Getter, _ => null), Is.EqualTo(1));
        Assert.That(read.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(consume.OpCode, Is.EqualTo(OpCode.Nop));
        var holderSignature = new ByReferenceTypeSignature(holderDefinition.ToTypeSignature(true));
        var snapshotDefinition = new MethodDefinition("Snapshot", AMethod.Public | AMethod.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int64, [holderSignature]));
        owner.Methods.Add(snapshotDefinition); snapshotDefinition.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var snapshotLocals = new Dictionary<LocalVariable, CilLocalVariable>();
        foreach (var local in snapshot.Locals)
        {
            var storage = new CilLocalVariable(ReferenceEquals(local, holderLocal) ? holderSignature
                : ReferenceEquals(local.Type, f.Type) ? data.ToTypeSignature(true) : module.CorLibTypeFactory.Int64);
            snapshotLocals.Add(local, storage); snapshotDefinition.CilMethodBody.LocalVariables.Add(storage);
        }
        snapshotDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        snapshotDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Stloc, snapshotLocals[holderLocal]);
        foreach (var instruction in snapshot.ControlFlowGraph.Instructions)
            emit.Invoke(null, [instruction, snapshot, snapshotDefinition, snapshotLocals, snapshotDefinition]);
        using var stream = new MemoryStream(); module.Write(stream);
        var generated = Assembly.Load(stream.ToArray()); var word = generated.GetType("Fixture.Word")!;
        var calculate = generated.GetType("Fixture.Generated")!.GetMethod("Calculate")!;
        foreach (var bits in new[] { 0UL, 123456UL, 0x4000000000000001UL, 0x8000000000000001UL, ulong.MaxValue })
        foreach (var offsetTicks in new[] { 0L, 5L, -5L, long.MinValue })
        {
            var a = Activator.CreateInstance(word)!; var b = Activator.CreateInstance(word)!;
            word.GetField("Payload")!.SetValue(a, bits); word.GetField("Payload")!.SetValue(b, unchecked((ulong)offsetTicks));
            var expected = unchecked((long)(bits & (ulong)NativeScalarValueRecovery.TicksMask) - offsetTicks);
            Assert.That(calculate.Invoke(null, [a, b]), Is.EqualTo(expected));
        }
        var holderRuntime = generated.GetType("Fixture.Holder")!;
        var snapshotRuntime = generated.GetType("Fixture.Generated")!.GetMethod("Snapshot")!;
        foreach (var bits in new[] { 1UL, 123456UL, 0x8000000000000005UL, ulong.MaxValue })
        {
            var holderValue = Activator.CreateInstance(holderRuntime)!;
            var originalValue = Activator.CreateInstance(word)!;
            word.GetField("Payload")!.SetValue(originalValue, bits);
            holderRuntime.GetField("Value")!.SetValue(holderValue, originalValue);
            object?[] arguments = [holderValue];
            Assert.That(snapshotRuntime.Invoke(null, arguments), Is.EqualTo((long)(bits & (ulong)NativeScalarValueRecovery.TicksMask)));
            var afterWrite = holderRuntime.GetField("Value")!.GetValue(arguments[0])!;
            Assert.That(word.GetField("Payload")!.GetValue(afterWrite), Is.EqualTo(0UL));
        }
    }

    [TestCase("adjacent-mask", true)]
    [TestCase("adjacent-subtract", true)]
    [TestCase("call-barrier", true)]
    [TestCase("write-barrier", true)]
    [TestCase("cross-block", true)]
    [TestCase("non-dominating", false)]
    [TestCase("late-load", false)]
    [TestCase("second-use", false)]
    [TestCase("escaped-address", false)]
    [TestCase("nested-use", false)]
    [TestCase("second-definition", false)]
    [TestCase("unknown-read-width", false)]
    [TestCase("narrow-read", false)]
    [TestCase("static-field", false)]
    [TestCase("reference-receiver", false)]
    [TestCase("parameter-snapshot", false)]
    public void ProjectionAtTheDominatingReadPreservesSingleUseSnapshotsAcrossInterleaving(string shape, bool direct)
    {
        var f = Fixture(); var t = f.Type.AppContext.SystemTypes;
        var holder = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Holder",
            t.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var field = holder.InjectFieldContext("Value", f.Type, FieldAttributes.Public
            | (shape == "static-field" ? FieldAttributes.Static : 0)); field.Offset = 8;
        var receiver = new LocalVariable("holder", new(null, "holder"),
            shape == "reference-receiver" ? holder : new ByRefTypeAnalysisContext(holder));
        var source = new LocalVariable("snapshot", new(null, "snapshot"), f.Type);
        var result = new LocalVariable("result", new(null, "result"), t.SystemInt64Type);
        var access = new FieldReference(field, receiver, 8);
        var load = new Instruction(0, OpCode.Move, source, access)
            { NativeReadSize = shape == "unknown-read-width" ? 0 : shape == "narrow-read" ? 4 : 8 };
        var raw = shape == "adjacent-subtract";
        var operation = new Instruction(1, raw ? OpCode.Subtract : OpCode.And, result, source,
            new Immediate(raw ? 5 : NativeScalarValueRecovery.TicksMask)) { NativeArithmeticSize = 8 };
        var method = new InjectedMethodAnalysisContext(t.SystemObjectType, "Project", t.SystemInt64Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new([load, operation, new(2, OpCode.Return, result)]),
            Locals = [receiver, source, result], ParameterLocals = shape == "parameter-snapshot" ? [receiver, source] : [receiver]
        };
        var block = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(operation));
        if (shape == "call-barrier") block.Instructions.Insert(1, new(-1, OpCode.CallVoid, f.Getter));
        if (shape == "write-barrier") block.Instructions.Insert(1,
            new(-1, OpCode.Move, access, new DefaultStructValue(f.Type)));
        if (shape == "late-load") { block.Instructions.Remove(load); block.Instructions.Insert(1, load); }
        if (shape == "cross-block")
        {
            operation.Index = 2;
            method.ControlFlowGraph = new([load, new(1, OpCode.Jump, operation), operation, new(3, OpCode.Return, result)]);
            block = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(operation));
        }
        if (shape == "non-dominating")
        {
            load.Index = 1; operation.Index = 3;
            var condition = new LocalVariable("condition", new(null, "condition"), t.SystemBooleanType);
            method.ControlFlowGraph = new([new(0, OpCode.ConditionalJump, operation, condition), load,
                new(2, OpCode.Jump, operation), operation, new(4, OpCode.Return, result)]);
            block = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(operation));
        }
        if (shape is "cross-block" or "non-dominating")
        {
            Assert.That(block.Predecessors, Is.Not.Empty, "The consumer must actually be reachable in this fixture");
            var producer = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(load));
            Assert.That(new Cpp2IL.Core.Graphs.DominatorInfo(method.ControlFlowGraph).Dominates(producer, block),
                Is.EqualTo(shape == "cross-block"));
        }
        if (shape is "second-use" or "escaped-address" or "nested-use")
        {
            IOperand other = shape == "escaped-address" ? new AddressOf(source)
                : shape == "nested-use" ? new FieldReference(f.Field, source, 0) : source;
            block.Instructions.Insert(block.Instructions.Count - 1, new(3, OpCode.CallVoid, f.Getter, other));
        }
        if (shape == "second-definition") block.Instructions.Insert(block.Instructions.Count - 1,
            new(3, OpCode.Move, source, new DefaultStructValue(f.Type)));
        Assert.That(NativeScalarValueRecovery.Recover(method, (_, _) => f.Getter, _ => f.Getter), Is.EqualTo(1));
        var call = direct ? load : raw ? block.Instructions[block.Instructions.IndexOf(operation) - 1] : operation;
        Assert.That(((AddressOf)call.Operands[2]).Target, Is.SameAs<IOperand>(direct ? access : source));
        Assert.That(load.OpCode, Is.EqualTo(direct ? OpCode.Call : OpCode.Move));
        if (direct && !raw) Assert.That(operation.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(source.Type, Is.SameAs(f.Type));
    }
}
