using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class VirtualDelegateRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("closed-string", true)]
    [TestCase("closed-int", false)]
    [TestCase("closed-open", false)]
    [TestCase("closed-argument", true)]
    [TestCase("closed-argument-wrong", false)]
    [TestCase("function-half", false)]
    [TestCase("misaligned", false)]
    [TestCase("unknown-slot", false)]
    [TestCase("narrow-pointer", false)]
    [TestCase("narrow-class", false)]
    [TestCase("duplicate-pointer", false)]
    [TestCase("duplicate-class", false)]
    [TestCase("rewritten-this", false)]
    [TestCase("not-this", false)]
    [TestCase("not-incoming", false)]
    [TestCase("wrong-receiver", false)]
    [TestCase("wrong-class-type", false)]
    [TestCase("class-offset", false)]
    [TestCase("indexed-load", false)]
    [TestCase("wrong-layout", false)]
    [TestCase("extra-use", false)]
    [TestCase("pointer-escape", false)]
    [TestCase("this-escape", false)]
    [TestCase("wrong-invoke", false)]
    [TestCase("wrong-constructor", false)]
    [TestCase("unknown-delegate", false)]
    [TestCase("not-dominating", false)]
    [TestCase("missing-allocation", false)]
    [TestCase("duplicate-allocation", false)]
    [TestCase("wrong-allocation-type", false)]
    [TestCase("early-object-use", false)]
    [TestCase("late-allocation", false)]
    [TestCase("not-allocation", false)]
    public void OnlyExactImmutableThisAndMethodInfoDelegateContractsAreRewritten(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game(); var t = app.SystemTypes;
        var owner = t.SystemObjectType;
        var target = shape.StartsWith("closed-argument", StringComparison.Ordinal)
            ? owner.Methods.Single(m => m.Name == "Equals" && m.IsVirtual && m.Parameters.Count == 1)
            : owner.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0);
        var multicast = owner.DeclaringAssembly.GetTypeByFullName("System.MulticastDelegate")!;
        var delegateDefinition = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Fixture", "Callback", multicast, TypeAttributes.Public);
        TypeAnalysisContext delegateType = delegateDefinition;
        MethodAnalysisContext constructor = new InjectedMethodAnalysisContext(delegateDefinition, ".ctor", t.SystemVoidType,
            MethodAttributes.Public, [t.SystemObjectType, t.SystemIntPtrType]);
        TypeAnalysisContext resultType = shape == "wrong-invoke" ? t.SystemInt32Type : t.SystemStringType;
        TypeAnalysisContext[] invokeParameters = [];
        if (shape.StartsWith("closed-", StringComparison.Ordinal))
        {
            var parameter = new GenericParameterTypeAnalysisContext("TResult", 0,
                LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, GenericParameterAttributes.None, delegateDefinition);
            delegateDefinition.GenericParameters.Add(parameter); resultType = parameter;
            var argument = shape == "closed-int" ? t.SystemInt32Type : shape == "closed-open" ? (TypeAnalysisContext)parameter : t.SystemStringType;
            List<TypeAnalysisContext> arguments = [argument];
            if (shape.StartsWith("closed-argument", StringComparison.Ordinal))
            {
                var input = new GenericParameterTypeAnalysisContext("TArgument", 1,
                    LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, GenericParameterAttributes.None, delegateDefinition);
                delegateDefinition.GenericParameters.Add(input); invokeParameters = [input];
                arguments = [t.SystemBooleanType, shape == "closed-argument-wrong" ? t.SystemInt32Type : t.SystemObjectType];
            }
            delegateType = new GenericInstanceTypeAnalysisContext(delegateDefinition, arguments);
            Assert.That(delegateType.Methods, Is.Empty, "real closed contexts resolve members on their metadata definition");
        }
        var invoke = new InjectedMethodAnalysisContext(delegateDefinition, "Invoke", resultType, MethodAttributes.Public, invokeParameters);
        delegateDefinition.Methods.Add(constructor); delegateDefinition.Methods.Add(invoke);
        if (delegateType is GenericInstanceTypeAnalysisContext closed)
            constructor = new ConcreteGenericMethodAnalysisContext(constructor, closed.GenericArguments, []);
        var receiver = new LocalVariable("this", new(null, "X0"), owner) { IsThis = true };
        var other = new LocalVariable("other", new(null, "X4"), owner);
        var klass = new LocalVariable("klass", new(null, "X8"), new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var pointer = new LocalVariable("methodInfo", new(null, "X2"), t.SystemIntPtrType);
        var obj = new LocalVariable("callback", new(null, "X5"), delegateType);
        var allocation = new Instruction(0, OpCode.Newobj, obj, delegateType);
        var classLoad = new Instruction(1, OpCode.Move, klass, new MemoryOperand(receiver)) { NativeReadSize = 8 };
        var offset = 0x128 + 16L * target.Definition!.slot + 8;
        var pointerLoad = new Instruction(2, OpCode.Move, pointer, new MemoryOperand(klass, addend: offset)) { NativeReadSize = 8 };
        var call = new Instruction(3, OpCode.CallVoid, constructor, obj, receiver, pointer);
        var graph = new ISILControlFlowGraph([allocation, classLoad, pointerLoad, call, new(4, OpCode.Return)]);
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", t.SystemVoidType, MethodAttributes.Public, [])
            { ControlFlowGraph = graph, ParameterLocals = [receiver], Locals = [receiver, other, klass, pointer, obj] };
        var block = graph.Blocks.Single(b => b.Instructions.Contains(call));
        var layout = RuntimeMetadataLayout.For(new UnityVersion(2018, 4, 28, UnityVersionType.Final, 1), 8);
        if (shape == "function-half") pointerLoad.SetOperand(1, new MemoryOperand(klass, addend: offset - 8));
        if (shape == "misaligned") pointerLoad.SetOperand(1, new MemoryOperand(klass, addend: offset + 1));
        if (shape == "unknown-slot") pointerLoad.SetOperand(1, new MemoryOperand(klass, addend: offset + 0x100000));
        if (shape == "narrow-pointer") pointerLoad.NativeReadSize = 4;
        if (shape == "narrow-class") classLoad.NativeReadSize = 4;
        if (shape == "duplicate-pointer") block.Instructions.Insert(0, new(0, OpCode.Move, pointer, new Immediate(1)));
        if (shape == "duplicate-class") block.Instructions.Insert(0, new(0, OpCode.Move, klass, other));
        if (shape == "rewritten-this") block.Instructions.Insert(0, new(0, OpCode.Move, receiver, other));
        if (shape == "not-this") receiver.IsThis = false;
        if (shape == "not-incoming") caller.ParameterLocals = [];
        if (shape == "wrong-receiver") call.SetOperand(2, other);
        if (shape == "wrong-class-type") klass.Type = new RuntimeClassTypeAnalysisContext(t.SystemStringType, owner.DeclaringAssembly);
        if (shape == "class-offset") classLoad.SetOperand(1, new MemoryOperand(receiver, addend: 8));
        if (shape == "indexed-load") pointerLoad.SetOperand(1, new MemoryOperand(klass, other, offset, 8));
        if (shape == "wrong-layout") layout = layout with { VTable = 0x138 };
        if (shape == "extra-use") block.Instructions.Add(new(4, OpCode.Return, pointer));
        if (shape == "pointer-escape") block.Instructions.Add(new(4, OpCode.Return, new AddressOf(pointer)));
        if (shape == "this-escape") block.Instructions.Add(new(4, OpCode.Return, new AddressOf(receiver)));
        if (shape == "wrong-constructor") call.AddOperands([new Immediate(0)]);
        if (shape == "unknown-delegate") obj.Type = null;
        if (shape == "not-dominating") { block.Instructions.Remove(pointerLoad); block.Instructions.Add(pointerLoad); }
        if (shape == "missing-allocation") block.Instructions.Remove(allocation);
        if (shape == "duplicate-allocation") block.Instructions.Insert(0, new(0, OpCode.Newobj, obj, delegateType));
        if (shape == "wrong-allocation-type") allocation.SetOperand(1, owner);
        if (shape == "early-object-use") block.Instructions.Insert(1, new(0, OpCode.CallVoid, new Immediate(1234), obj));
        if (shape == "late-allocation") { block.Instructions.Remove(allocation); block.Instructions.Insert(2, allocation); }
        if (shape == "not-allocation") { allocation.OpCode = OpCode.Move; allocation.SetOperands(obj, new Immediate(0)); }
        var before = graph.Instructions.Select(i => i.ToString()).ToArray();
        Assert.That(VirtualDelegateRecovery.Run(caller, layout), Is.EqualTo(expected ? 1 : 0));
        if (!expected) Assert.That(graph.Instructions.Select(i => i.ToString()), Is.EqualTo(before));
        else
        {
            Assert.That(allocation.OpCode, Is.EqualTo(OpCode.NewVirtualDelegate));
            Assert.That(allocation.Destination, Is.SameAs(obj));
            Assert.That(allocation.Sources.ToArray(), Is.EqualTo(new IOperand[] { receiver }));
            Assert.That(allocation.Operands[2], Is.SameAs(target));
            Assert.That(pointerLoad.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(call.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(VirtualDelegateRecovery.Run(caller, layout), Is.Zero);
            DeadCodeEliminator.Run(caller);
            Assert.That(allocation.OpCode, Is.EqualTo(OpCode.NewVirtualDelegate));
        }
    }

    [TestCase("pointer")]
    [TestCase("atomic")]
    [TestCase("legacy")]
    public void EmittedFunctionPointerUsesRuntimeOverrideRatherThanBaseAndChecksNull(string mode)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var assembly = new AssemblyDefinition("VirtualDelegate" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("VirtualDelegate.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var baseType = new TypeDefinition("Fixture", "Base", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        var derived = new TypeDefinition("Fixture", "Derived", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, baseType);
        module.TopLevelTypes.Add(baseType); module.TopLevelTypes.Add(derived);
        MethodDefinition Constructor(TypeDefinition type, ITypeDefOrRef parent)
        {
            var ctor = new MethodDefinition(".ctor", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
                MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)); type.Methods.Add(ctor);
            ctor.CilMethodBody = new CilMethodBody(); ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call, parent.CreateMemberReference(".ctor", MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)));
            ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret); return ctor;
        }
        Constructor(baseType, module.CorLibTypeFactory.Object.Type); Constructor(derived, baseType);
        MethodDefinition Target(TypeDefinition type, string value, bool newSlot)
        {
            var method = new MethodDefinition("Target", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Virtual | (newSlot ? AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.NewSlot : 0),
                MethodSignature.CreateInstance(module.CorLibTypeFactory.String)); type.Methods.Add(method);
            method.CilMethodBody = new CilMethodBody(); method.CilMethodBody.Instructions.Add(CilOpCodes.Ldstr, value);
            method.CilMethodBody.Instructions.Add(CilOpCodes.Ret); return method;
        }
        var baseTarget = Target(baseType, "base", true); Target(derived, "derived", false);
        var owner = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Base", t.SystemObjectType, TypeAttributes.Public);
        owner.PutExtraData("AsmResolverType", baseType);
        var target = new InjectedMethodAnalysisContext(owner, "Target", t.SystemStringType, MethodAttributes.Public | MethodAttributes.Virtual, []);
        target.PutExtraData("AsmResolverMethod", baseTarget);
        TypeSignature func = module.DefaultImporter.ImportTypeSignature(typeof(Func<string>));
        InjectedTypeAnalysisContext? callbackContext = null;
        MethodAnalysisContext? callbackConstructor = null;
        if (mode != "pointer")
        {
            var callbackType = new TypeDefinition("Fixture", "Callback", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Sealed,
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "MulticastDelegate"));
            module.TopLevelTypes.Add(callbackType); func = callbackType.ToTypeSignature(false);
            var ctor = new MethodDefinition(".ctor", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
                MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Object, module.CorLibTypeFactory.IntPtr]))
                { ImplAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodImplAttributes.Runtime };
            callbackType.Methods.Add(ctor);
            callbackType.Methods.Add(new MethodDefinition("Invoke", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Virtual | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.NewSlot,
                MethodSignature.CreateInstance(module.CorLibTypeFactory.String))
                { ImplAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodImplAttributes.Runtime });
            callbackContext = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Fixture", "Callback",
                t.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.MulticastDelegate"), TypeAttributes.Public | TypeAttributes.Sealed);
            callbackContext.PutExtraData("AsmResolverType", callbackType);
            callbackConstructor = new InjectedMethodAnalysisContext(callbackContext, ".ctor", t.SystemVoidType,
                MethodAttributes.Public, [t.SystemObjectType, t.SystemIntPtrType]);
            callbackConstructor.PutExtraData("AsmResolverMethod", ctor);
        }
        var factory = new MethodDefinition("Create", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static, MethodSignature.CreateStatic(func, [baseType.ToTypeSignature(false)]));
        baseType.Methods.Add(factory); factory.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        var receiver = new LocalVariable("receiver", new(null, "X0"), owner) { ParameterIndex = 0 };
        var pointer = new LocalVariable("pointer", new(null, "X2"), t.SystemIntPtrType);
        var pointerSlot = new CilLocalVariable(module.CorLibTypeFactory.IntPtr); factory.CilMethodBody.LocalVariables.Add(pointerSlot);
        var context = new InjectedMethodAnalysisContext(owner, "Create", t.SystemObjectType, MethodAttributes.Public | MethodAttributes.Static, [owner])
            { ParameterLocals = [receiver], Locals = [receiver, pointer] };
        var emit = typeof(IlGenerator).GetMethod("GenerateInstructions", BindingFlags.NonPublic | BindingFlags.Static)!;
        var slots = new Dictionary<LocalVariable, CilLocalVariable> { [pointer] = pointerSlot };
        if (mode == "pointer")
        {
            emit.Invoke(null, [new Instruction(0, OpCode.LoadVirtualFunction, pointer, target, receiver), context, factory, slots, factory]);
            factory.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0); factory.CilMethodBody.Instructions.Add(CilOpCodes.Ldloc, pointerSlot);
            factory.CilMethodBody.Instructions.Add(CilOpCodes.Newobj, module.DefaultImporter.ImportMethod(typeof(Func<string>).GetConstructors().Single()));
        }
        else
        {
            var callback = new LocalVariable("callback", new(null, "X5"), callbackContext);
            var callbackSlot = new CilLocalVariable(func); slots[callback] = callbackSlot;
            factory.CilMethodBody.LocalVariables.Add(callbackSlot);
            if (mode == "atomic")
                emit.Invoke(null, [new Instruction(0, OpCode.NewVirtualDelegate, callback, callbackConstructor!, target, receiver), context, factory, slots, factory]);
            else
            {
                var allocation = new Instruction(0, OpCode.Newobj, callback, callbackContext!);
                var load = new Instruction(1, OpCode.LoadVirtualFunction, pointer, target, receiver);
                var call = new Instruction(2, OpCode.CallVoid, callbackConstructor!, callback, receiver, pointer);
                context.ControlFlowGraph = new ISILControlFlowGraph([allocation, load, call, new(3, OpCode.Return, callback)]);
                foreach (var instruction in new[] { allocation, load, call })
                    emit.Invoke(null, [instruction, context, factory, slots, factory]);
            }
            factory.CilMethodBody.Instructions.Add(CilOpCodes.Ldloc, callbackSlot);
        }
        Assert.That(factory.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Ldvirtftn), Is.True);
        Assert.That(factory.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False);
        factory.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        using var stream = new MemoryStream(); module.Write(stream);
        var loaded = Assembly.Load(stream.ToArray()); var create = loaded.GetType("Fixture.Base")!.GetMethod("Create")!;
        var instance = Activator.CreateInstance(loaded.GetType("Fixture.Derived")!);
        if (mode == "legacy")
        {
            var premature = Assert.Throws<TargetInvocationException>(() => create.Invoke(null, [instance]));
            Assert.That(premature!.InnerException, Is.TypeOf<ArgumentNullException>(), "counterexample: old early fusion consumed zero future pointer");
            return;
        }
        var constructedCallback = (Delegate)create.Invoke(null, [instance])!;
        Assert.That(constructedCallback.DynamicInvoke(), Is.EqualTo("derived"));
        var error = Assert.Throws<TargetInvocationException>(() => create.Invoke(null, [null]));
        Assert.That(error!.InnerException, Is.TypeOf<NullReferenceException>());
    }
}
