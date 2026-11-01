using System.Linq;
using System.Reflection;
using System;
using System.IO;
using System.Collections.Generic;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Utils.AsmResolver;
using AsmTypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AsmFieldAttributes = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using AsmMethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StructArrayComponentTests
{
    private static (MethodAnalysisContext Method, Instruction Access, LocalVariable Array) Create(
        bool store, bool dynamicIndex, int offset, int width, int stride = 12)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var vector = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "UnityEngine.Vector3");
        var array = new LocalVariable("array", new Register(null, "X19"), new SzArrayTypeAnalysisContext(vector));
        var index = new LocalVariable("index", new Register(null, "W1"), app.SystemTypes.SystemInt32Type);
        var value = new LocalVariable("value", new Register(null, "S0"));
        var scaled = new LocalVariable("scaled", new Register(null, "scaled"));
        var address = new LocalVariable("address", new Register(null, "X8"));
        var memory = new MemoryOperand(dynamicIndex ? address : array, addend: offset);
        var access = store ? new Instruction(2, OpCode.Move, memory, value) { NativeWriteSize = width }
            : new Instruction(2, OpCode.Move, value, memory) { NativeReadSize = width };
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "ReadWrite",
            store ? app.SystemTypes.SystemVoidType : app.SystemTypes.SystemSingleType, MethodAttributes.Public | MethodAttributes.Static, []);
        var ret = store ? new Instruction(3, OpCode.Return) : new Instruction(3, OpCode.Return, value);
        method.ControlFlowGraph = dynamicIndex
            ? new([new(0, OpCode.Multiply, scaled, index, new Immediate(stride)),
                new(1, OpCode.Add, address, array, scaled), access, ret])
            : new([access, ret]);
        method.Locals = [array, index, value, scaled, address];
        return (method, access, array);
    }

    [TestCase(false, false, 32, "x", 0)]
    [TestCase(false, false, 36, "y", 0)]
    [TestCase(false, false, 52, "z", 1)]
    [TestCase(true, false, 36, "y", 0)]
    [TestCase(false, true, 40, "z", -1)]
    [TestCase(true, true, 36, "y", -1)]
    public void ExactComponentUsesManagedElementAddress(bool store, bool dynamicIndex, int offset, string fieldName, int constantIndex)
    {
        var (method, access, array) = Create(store, dynamicIndex, offset, 4);
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.True);
        var field = access.Operands[store ? 0 : 1] as FieldReference;
        Assert.That(field?.Field.Name, Is.EqualTo(fieldName));
        Assert.That(field?.Local.Type, Is.TypeOf<ByRefTypeAnalysisContext>());
        var prefix = method.ControlFlowGraph!.Instructions.Single(i => ReferenceEquals(i.Destination, field!.Local));
        var element = ((AddressOf)prefix.Operands[1]).Target as ArrayAccess;
        Assert.That(element?.Array, Is.SameAs(array));
        if (constantIndex >= 0) Assert.That(((Immediate)element!.Index).Value, Is.EqualTo(constantIndex));
        else Assert.That(((LocalVariable)element!.Index).Name, Is.EqualTo("index"));
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.False, "lowering is idempotent");
        DeadCodeEliminator.Run(method);
        Assert.That(prefix.OpCode, Is.EqualTo(OpCode.Move), "the field read/store keeps its address alive");
    }

    [TestCase(32, 2, 12)] // Partial scalar.
    [TestCase(34, 4, 12)] // Misaligned/cross-field.
    [TestCase(40, 8, 12)] // Cross-element range.
    [TestCase(32, 12, 12)] // Whole struct, not a component.
    [TestCase(32, 0, 12)] // Unknown native width.
    [TestCase(24, 4, 12)] // Array header.
    [TestCase(36, 4, 8)] // Wrong dynamic stride.
    public void UnprovenRangeRemainsDiagnostic(int offset, int width, int stride)
    {
        var (method, access, _) = Create(false, true, offset, width, stride);
        var count = method.ControlFlowGraph!.Instructions.Count;
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.False);
        Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(method.ControlFlowGraph.Instructions.Count, Is.EqualTo(count));
    }

    [Test]
    public void TypeFixpointDoesNotPoisonScalarWithWholeStructureType()
    {
        var (method, access, _) = Create(false, false, 36, 4);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(access.Operands[1], Is.TypeOf<FieldReference>());
        Assert.That(((LocalVariable)access.Operands[0]).Type?.FullName, Is.EqualTo("System.Single"));
    }

    [Test]
    public void InstructionBranchTargetIncludesAddressInitialization()
    {
        var (method, access, _) = Create(true, false, 36, 4);
        var branch = new Instruction(4, OpCode.Jump, access);
        method.ControlFlowGraph!.EntryBlock.Instructions.Add(branch);
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.True);
        var target = branch.Operands[0] as Instruction;
        Assert.That(target?.Operands[1], Is.TypeOf<AddressOf>());
        Assert.That(target, Is.Not.SameAs(access));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ReferenceComponentRequiresAnExactPointerSlot(bool partial)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var entry = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.Collections.DictionaryEntry");
        var field = entry.Fields.First(f => !f.IsStatic && !f.FieldType.IsValueType);
        var array = new LocalVariable("array", new Register(null, "X19"), new SzArrayTypeAnalysisContext(entry));
        var result = new LocalVariable("result", new Register(null, "X0"));
        var access = new Instruction(0, OpCode.Move, result, new MemoryOperand(array, addend: 32 + field.Offset))
            { NativeReadSize = partial ? 4 : 8 };
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read", app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new([access, new(1, OpCode.Return, result)]);
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.EqualTo(!partial));
        if (!partial) Assert.That(((FieldReference)access.Operands[1]).Field, Is.SameAs(field));
        else Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void ExistingConflictingResultTypeIsNotOverwritten()
    {
        var (method, access, _) = Create(false, false, 36, 4);
        var app = method.AppContext;
        ((LocalVariable)access.Operands[0]).Type = app.SystemTypes.SystemInt32Type;
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.False);
        Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(((LocalVariable)access.Operands[0]).Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
    }

    [Test]
    public void MultiplyDefinedAddressIsNotFlattenedAcrossDifferentValues()
    {
        var (method, access, _) = Create(false, true, 36, 4);
        var address = ((MemoryOperand)access.Operands[1]).Base!;
        var block = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(access));
        block.Instructions.Insert(2, new Instruction(5, OpCode.Move, address, new Immediate(0)));
        Assert.That(ArrayRecovery.RecoverStructComponents(method), Is.False);
        Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void GeneratedManagedIlReadsAndWritesActualElementStorage(bool store)
    {
        var (context, access, _) = Create(store, true, 36, 4);
        // This isolated emitter fixture declares its CLR signature below and
        // bypasses CreateAll, so explicitly identify its incoming values.
        context.Locals.Single(l=>l.Name=="array").ParameterIndex=0;
        context.Locals.Single(l=>l.Name=="index").ParameterIndex=1;
        if(store)context.Locals.Single(l=>l.Name=="value").ParameterIndex=2;
        Assert.That(ArrayRecovery.RecoverStructComponents(context), Is.True);
        var field = (FieldReference)access.Operands[store ? 0 : 1];
        var vector = field.Field.DeclaringType;
        var assembly = new AssemblyDefinition("StructArray" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("StructArray.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var vectorDef = new TypeDefinition("Test", "Vector", AsmTypeAttributes.Public | AsmTypeAttributes.SequentialLayout,
            new TypeReference(module, module.CorLibTypeFactory.CorLibScope, "System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        foreach (var component in vector.Fields.Where(f => !f.IsStatic))
        {
            var definition = new FieldDefinition(component.Name, AsmFieldAttributes.Public, new FieldSignature(module.CorLibTypeFactory.Single));
            vectorDef.Fields.Add(definition);
            component.PutExtraData("AsmResolverField", definition);
        }
        var generated = new TypeDefinition("Test", "Generated", AsmTypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(generated);
        var arguments = new List<TypeSignature> { new SzArrayTypeSignature(vectorDef.ToTypeSignature()), module.CorLibTypeFactory.Int32 };
        if (store) arguments.Add(module.CorLibTypeFactory.Single);
        var method = new MethodDefinition("Access", AsmMethodAttributes.Public | AsmMethodAttributes.Static,
            MethodSignature.CreateStatic(store ? module.CorLibTypeFactory.Void : module.CorLibTypeFactory.Single, arguments.ToArray()));
        generated.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "array", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "index", 0));
        if (store) method.ParameterDefinitions.Add(new ParameterDefinition(3, "value", 0));
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var addressLocal = new CilLocalVariable(new ByReferenceTypeSignature(vectorDef.ToTypeSignature()));
        method.CilMethodBody.LocalVariables.Add(addressLocal);
        var locals = new Dictionary<LocalVariable, CilLocalVariable> { { field.Local, addressLocal } };
        if (!store)
        {
            var result = new CilLocalVariable(module.CorLibTypeFactory.Single);
            method.CilMethodBody.LocalVariables.Add(result);
            locals[(LocalVariable)access.Operands[0]] = result;
        }
        DeadCodeEliminator.Run(context);
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        foreach (var instruction in context.ControlFlowGraph!.Instructions.Where(i => i.OpCode != OpCode.Nop))
            emit.Invoke(null, [instruction, context, method, locals, method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Ldelema), Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == (store ? CilOpCodes.Stfld : CilOpCodes.Ldfld)), Is.True);
        using var stream = new MemoryStream();
        module.Write(stream);
        // Execute only this freshly generated fixture, never any game assembly.
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        var runtimeVector = loaded.GetType("Test.Vector")!;
        var array = Array.CreateInstance(runtimeVector, 2);
        var vectorValue = Activator.CreateInstance(runtimeVector)!;
        runtimeVector.GetField("x")!.SetValue(vectorValue, 11f);
        runtimeVector.GetField("y")!.SetValue(vectorValue, 22f);
        runtimeVector.GetField("z")!.SetValue(vectorValue, 33f);
        array.SetValue(vectorValue, 1);
        var execute = loaded.GetType("Test.Generated")!.GetMethod("Access")!;
        if (store) execute.Invoke(null, [array, 1, 99f]);
        else Assert.That(execute.Invoke(null, [array, 1]), Is.EqualTo(22f));
        Assert.That(runtimeVector.GetField("x")!.GetValue(array.GetValue(1)), Is.EqualTo(11f));
        Assert.That(runtimeVector.GetField("y")!.GetValue(array.GetValue(1)), Is.EqualTo(store ? 99f : 22f));
        Assert.That(runtimeVector.GetField("z")!.GetValue(array.GetValue(1)), Is.EqualTo(33f));
    }
}
