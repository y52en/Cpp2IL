using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using Cpp2IL.Core.Analysis;
using AType = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AField = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using AMethod = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class FieldReferenceAddressEmissionTests
{
    private static (Type Generated, MethodInfo Run, bool Nested) Build(bool isStatic, bool nested, bool optimize = false, bool unused = false, bool observe = false)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        // Register real corlib signatures before the full GenerateIl local-map path.
        _ = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var types = app.SystemTypes;
        var holder = new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,
            "Fixture", "Holder", types.SystemObjectType, TypeAttributes.Public);
        var data = new InjectedTypeAnalysisContext(holder.DeclaringAssembly,
            "Fixture", "Data", types.SystemValueTypeType, TypeAttributes.Public | TypeAttributes.SequentialLayout);
        var assembly = new AssemblyDefinition("FieldAddress" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("FieldAddress.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var holderDef = new TypeDefinition("Fixture", "Holder", AType.Public, module.CorLibTypeFactory.Object.Type);
        var dataDef = new TypeDefinition("Fixture", "Data", AType.Public | AType.Sealed | AType.SequentialLayout,
            new TypeReference(module, module.CorLibTypeFactory.CorLibScope, "System", "ValueType"));
        module.TopLevelTypes.Add(holderDef); module.TopLevelTypes.Add(dataDef);
        holder.PutExtraData("AsmResolverType", holderDef); data.PutExtraData("AsmResolverType", dataDef);
        var root = new LocalVariable("only-address-receiver", new Register(null, "root"), holder) { ParameterIndex = 0 };
        var attrs = FieldAttributes.Public | (isStatic ? FieldAttributes.Static : 0);
        FieldReference addressed;
        if (nested)
        {
            var parent = holder.InjectFieldContext("Data", data, attrs);
            var leaf = data.InjectFieldContext("X", types.SystemInt32Type, FieldAttributes.Public);
            var parentDef = new FieldDefinition("Data", AField.Public | (isStatic ? AField.Static : 0), new FieldSignature(dataDef.ToTypeSignature(true)));
            var leafDef = new FieldDefinition("X", AField.Public, new FieldSignature(module.CorLibTypeFactory.Int32));
            holderDef.Fields.Add(parentDef); dataDef.Fields.Add(leafDef);
            parent.PutExtraData("AsmResolverField", parentDef); leaf.PutExtraData("AsmResolverField", leafDef);
            addressed = new FieldReference(leaf, root, 0) { Parent = new FieldReference(parent, root, 0) };
        }
        else
        {
            var field = holder.InjectFieldContext("X", types.SystemInt32Type, attrs);
            var fieldDef = new FieldDefinition("X", AField.Public | (isStatic ? AField.Static : 0), new FieldSignature(module.CorLibTypeFactory.Int32));
            holderDef.Fields.Add(fieldDef); field.PutExtraData("AsmResolverField", fieldDef);
            addressed = new FieldReference(field, root, 0);
        }
        var caller = new InjectedMethodAnalysisContext(holder, "Run", types.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, isStatic ? [] : [holder]);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), new ByRefTypeAnalysisContext(types.SystemInt32Type));
        var steps = new System.Collections.Generic.List<Instruction> {
            new(0, OpCode.Move, pointer, new AddressOf(addressed)),
            new(1, OpCode.Move, new MemoryOperand(pointer), new Immediate(49)), new(2, OpCode.Return) };
        if (unused) steps.RemoveAt(1);
        if (observe)
        {
            var counter = new FieldDefinition("Count", AField.Public | AField.Static, new FieldSignature(module.CorLibTypeFactory.Int32));
            holderDef.Fields.Add(counter);
            var record = new MethodDefinition("Record", AMethod.Public | AMethod.Static,
                MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
            holderDef.Methods.Add(record);
            record.CilMethodBody = new AsmResolver.DotNet.Code.Cil.CilMethodBody();
            record.CilMethodBody.Instructions.Add(CilOpCodes.Ldsfld, counter);
            record.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4_1);
            record.CilMethodBody.Instructions.Add(CilOpCodes.Add);
            record.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, counter);
            record.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
            var recordContext = holder.InjectMethodContext("Record", types.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static);
            recordContext.PutExtraData("AsmResolverMethod", record);
            steps.Insert(1, new(3, OpCode.CallVoid, recordContext));
        }
        LocalVariable? receiverCopy = null;
        if (optimize && addressed.RequiresReceiver)
        {
            receiverCopy = new LocalVariable("address_only_copy", new Register(null, "address_only_copy"), holder);
            addressed.ReplaceLocal(root, receiverCopy);
            steps.Insert(0, new(-1, OpCode.Move, receiverCopy, root) { NativeRegisterCopySize = 8 });
        }
        caller.ControlFlowGraph = new(steps);
        // No other IR operand mentions the receiver: GenerateIl must discover
        // it through AddressOf(FieldReference), including its parent chain.
        caller.Locals = []; caller.ParameterLocals = isStatic ? [] : [root]; caller.AnalysisWarnings = [];
        if (optimize)
        {
            caller.Locals.Add(root); caller.Locals.Add(pointer);
            if (receiverCopy != null) caller.Locals.Add(receiverCopy);
            DeadCodeEliminator.Run(caller); SsaSimplifier.Run(caller); DeadCodeEliminator.Run(caller);
            CopyCoalescer.Run(caller); Simplifier.Simplify(caller); LocalVariables.RemoveUnused(caller);
        }
        var signature = isStatic ? MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)
            : MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [holderDef.ToTypeSignature(false)]);
        var method = new MethodDefinition("Run", AMethod.Public | AMethod.Static, signature);
        holderDef.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand?.ToString()?.Contains("Unknown operand") == true), Is.False);
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldflda), Is.EqualTo(nested ? (isStatic ? 1 : 2) : (isStatic ? 0 : 1)));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldsflda), Is.EqualTo(isStatic ? 1 : 0));
        using var stream = new MemoryStream(); module.Write(stream);
        var generated = Assembly.Load(stream.ToArray()).GetType("Fixture.Holder")!;
        return (generated, generated.GetMethod("Run")!, nested);
    }

    [TestCase(false, false)]
    [TestCase(true, false)]
    [TestCase(false, true)]
    [TestCase(true, true)]
    public void ManagedFieldAddressWritesTheOriginalStorage(bool isStatic, bool nested)
    {
        var f = Build(isStatic, nested);
        var instance = isStatic ? null : RuntimeHelpers.GetUninitializedObject(f.Generated);
        f.Run.Invoke(null, isStatic ? [] : [instance]);
        var container = nested ? f.Generated.GetField("Data")!.GetValue(instance) : instance;
        var scalar = nested ? container!.GetType().GetField("X")! : f.Generated.GetField("X")!;
        Assert.That(scalar.GetValue(container), Is.EqualTo(49));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void NullInstanceStillThrowsAtTheFieldAddress(bool nested)
    {
        var f = Build(false, nested);
        var error = Assert.Throws<TargetInvocationException>(() => f.Run.Invoke(null, [null]));
        Assert.That(error!.InnerException, Is.TypeOf<NullReferenceException>());
    }

    [TestCase(false, false)]
    [TestCase(true, false)]
    [TestCase(false, true)]
    [TestCase(true, true)]
    public void OptimizersKeepTheActualReceiverAndWriteItsOriginalField(bool isStatic, bool nested)
    {
        var f = Build(isStatic, nested, true);
        var instance = isStatic ? null : RuntimeHelpers.GetUninitializedObject(f.Generated);
        f.Run.Invoke(null, isStatic ? [] : [instance]);
        var container = nested ? f.Generated.GetField("Data")!.GetValue(instance) : instance;
        var scalar = nested ? container!.GetType().GetField("X")! : f.Generated.GetField("X")!;
        Assert.That(scalar.GetValue(container), Is.EqualTo(49));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AnUnusedFieldAddressStillKeepsTheOriginalNullException(bool nested)
    {
        var f = Build(false, nested, true, true);
        var error = Assert.Throws<TargetInvocationException>(() => f.Run.Invoke(null, [null]));
        Assert.That(error!.InnerException, Is.TypeOf<NullReferenceException>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void FieldAddressNullExceptionPrecedesTheFollowingObservableCall(bool nested)
    {
        var f = Build(false, nested, true, true, true);
        var error = Assert.Throws<TargetInvocationException>(() => f.Run.Invoke(null, [null]));
        Assert.That(error!.InnerException, Is.TypeOf<NullReferenceException>());
        Assert.That(f.Generated.GetField("Count")!.GetValue(null), Is.EqualTo(0));
    }
}
