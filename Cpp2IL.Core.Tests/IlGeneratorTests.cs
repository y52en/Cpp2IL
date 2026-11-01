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
    [TestCase("exclusive")]
    [TestCase("unreachable")]
    [TestCase("redefined")]
    [TestCase("ambiguous")]
    public void ConstructorPairingUsesSuccessorsNotFlattenedBfsOrReusedLocal(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test","ReachableCtor",app.SystemTypes.SystemObjectType,System.Reflection.TypeAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public,[]);
        var context=new InjectedMethodAnalysisContext(owner,"Create",app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        var obj=new LocalVariable("reused",new Register(null,"X0"),owner);
        var allocationA=new Instruction(0,OpCode.Newobj,obj,owner);
        var allocationB=new Instruction(1,OpCode.Newobj,obj,owner);
        var callA=new Instruction(2,OpCode.CallVoid,ctor,obj);
        var callB=new Instruction(3,OpCode.CallVoid,ctor,obj);
        var graph=new ISILControlFlowGraph([]);
        var a=new Block{ID=2,Instructions=[allocationA]};var b=new Block{ID=3,Instructions=[allocationB]};
        var ca=new Block{ID=4,Instructions=[callA]};var cb=new Block{ID=5,Instructions=[callB]};
        void Edge(Block x,Block y){x.Successors.Add(y);y.Predecessors.Add(x);}
        Edge(graph.EntryBlock,a);
        if(shape=="redefined"){Edge(a,b);Edge(b,cb);}
        else if(shape=="ambiguous"){Edge(a,ca);Edge(a,cb);}
        else {Edge(graph.EntryBlock,b);Edge(b,cb);Edge(a,shape=="unreachable"?graph.ExitBlock:ca);}
        Edge(ca,graph.ExitBlock);Edge(cb,graph.ExitBlock);
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,a,b,ca,cb];context.ControlFlowGraph=graph;
        Assert.That(IlGenerator.FindConstructorCall(context,allocationA),Is.EqualTo(shape=="exclusive"?callA:null));
        if(shape!="ambiguous")Assert.That(IlGenerator.FindConstructorCall(context,allocationB),Is.SameAs(callB));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ConstructorFusionIsIndependentOfPhysicalBlockEmissionOrder(bool ctorBeforeAllocation)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test","CtorOrder",app.SystemTypes.SystemObjectType,System.Reflection.TypeAttributes.Public);
        var ctor=owner.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public,[]);
        var context=new InjectedMethodAnalysisContext(owner,"Create",app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        var obj=new LocalVariable("obj",new Register(null,"X0"),owner);
        var graph=new ISILControlFlowGraph([]);
        var start=new Block{ID=2};var allocation=new Block{ID=3};var construct=new Block{ID=4};var done=new Block{ID=5};
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,start);Edge(start,allocation);Edge(allocation,construct);Edge(construct,done);Edge(done,graph.ExitBlock);
        start.Instructions=[new(0,OpCode.Jump,allocation)];
        allocation.Instructions=[new(1,OpCode.Newobj,obj,owner),new(2,OpCode.Jump,construct)];
        construct.Instructions=[new(3,OpCode.CallVoid,ctor,obj),new(4,OpCode.Jump,done)];
        done.Instructions=[new(5,OpCode.Return)];
        graph.Blocks=ctorBeforeAllocation?[graph.EntryBlock,graph.ExitBlock,start,construct,allocation,done]
            :[graph.EntryBlock,graph.ExitBlock,start,allocation,construct,done];
        context.ControlFlowGraph=graph;context.Locals=[obj];context.ParameterLocals=[];context.AnalysisWarnings=[];
        var module=new ModuleDefinition("CtorOrder.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var type=new TypeDefinition("Test","CtorOrder",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);owner.PutExtraData("AsmResolverType",type);
        var ctorDef=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.SpecialName|MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        type.Methods.Add(ctorDef);ctor.PutExtraData("AsmResolverMethod",ctorDef);
        var method=new MethodDefinition("Create",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);IlGenerator.GenerateIl(context,method);
        var il=method.CilMethodBody!.Instructions;
        Assert.That(il.Count(i=>i.OpCode==CilOpCodes.Newobj),Is.EqualTo(1));
        Assert.That(il.Any(i=>i.OpCode==CilOpCodes.Call && i.Operand is IMethodDescriptor target && target.Name==".ctor"),Is.False);
        Assert.That(il.Last().OpCode,Is.EqualTo(CilOpCodes.Ret));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void UnresolvedIndirectTailTransferIsDiagnosticAndTerminal(bool returnsValue)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "UnresolvedTail", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var caller = new InjectedMethodAnalysisContext(owner, "Tail",
            returnsValue ? app.SystemTypes.SystemObjectType : app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new([new(0, OpCode.IndirectJump, new Immediate(123))]);
        caller.Locals = []; caller.ParameterLocals = []; caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("UnresolvedTail.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var type = new TypeDefinition("Test", "UnresolvedTail", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type); owner.PutExtraData("AsmResolverType", type);
        var method = new MethodDefinition("Tail", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnsValue ? module.CorLibTypeFactory.Object : module.CorLibTypeFactory.Void));
        type.Methods.Add(method); IlGenerator.GenerateIl(caller, method);
        var instructions = method.CilMethodBody!.Instructions;
        Assert.That(instructions.Last().OpCode, Is.EqualTo(CilOpCodes.Throw));
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Ret), Is.False);
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
            && text.Contains("Indirect jump:")), Is.True);
        Assert.That(instructions.Single(i => i.OpCode == CilOpCodes.Newobj).Operand,
            Is.InstanceOf<IMethodDescriptor>());
        Assert.That(((IMethodDescriptor)instructions.Single(i => i.OpCode == CilOpCodes.Newobj).Operand!).DeclaringType!.FullName,
            Is.EqualTo("System.NotSupportedException"));
    }

    [Test]
    public void ConstructorWithWrongOwnerDoesNotReplaceDerivedAllocation()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "DerivedAllocation", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var obj = new LocalVariable("obj", new Register(null, "obj"), owner);
        var baseConstructor = app.SystemTypes.SystemObjectType.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        var caller = new InjectedMethodAnalysisContext(owner, "Allocate", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new([new(0, OpCode.Newobj, obj, owner), new(1, OpCode.CallVoid, baseConstructor, obj), new(2, OpCode.Return)]);
        caller.Locals = [obj]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("ConstructorOwner.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var type = new TypeDefinition("Test", "DerivedAllocation", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type); owner.PutExtraData("AsmResolverType", type);
        var method = new MethodDefinition("Allocate", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)); type.Methods.Add(method);
        Assert.Throws<DecompilerException>(() => IlGenerator.GenerateIl(caller, method));
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
    }

    [Test]
    public void UnresolvedMemoryStore_EmitsDiagnosticInsteadOfSilentlyDiscardingWrite()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "UnresolvedStore", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var receiver = new LocalVariable("receiver", new Register(null, "X0"), owner);
        var caller = new InjectedMethodAnalysisContext(owner, "Write", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new([new(0, OpCode.Move, new MemoryOperand(receiver, addend: 24), new Immediate(37)),
            new(1, OpCode.Return)]);
        caller.Locals = [receiver]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("UnresolvedStore.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var type = new TypeDefinition("Test", "UnresolvedStore", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type); owner.PutExtraData("AsmResolverType", type);
        var method = new MethodDefinition("Write", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method); IlGenerator.GenerateIl(caller, method);
        var instructions = method.CilMethodBody!.Instructions;
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
            && text.Contains("Unmanaged memory store:")), Is.True);
        Assert.That(instructions.Count(i => i.OpCode == CilOpCodes.Pop), Is.EqualTo(1));
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Call), Is.True);
    }

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
        Assert.That(method.CilMethodBody.InitializeLocals, Is.True);
        Assert.That(method.CilMethodBody.LocalVariables.Count, Is.EqualTo(1), "No scratch struct for a local initialization");
    }

    [TestCase(false)]
    [TestCase(true)]
    public void DirectLocalInitializationClearsExistingValueAndManagedReferences(bool withReference)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "InitializedData", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.SequentialLayout);
        var number = context.InjectFieldContext("Number", app.SystemTypes.SystemInt64Type, System.Reflection.FieldAttributes.Public);
        var text = withReference ? context.InjectFieldContext("Text", app.SystemTypes.SystemStringType,
            System.Reflection.FieldAttributes.Public) : null;
        var local = new LocalVariable("value", new Register(null, "value"), context);
        var body = new List<Instruction> { new(0, OpCode.Move, new FieldReference(number, local, 0), new Immediate(99)) };
        if (text != null) body.Add(new(1, OpCode.Move, new FieldReference(text, local, 8), new StringLiteral("before")));
        body.Add(new(2, OpCode.Move, local, new DefaultStructValue(context)));
        body.Add(new(3, OpCode.Return, local));
        var caller = new InjectedMethodAnalysisContext(context, "Reset", context,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        { ControlFlowGraph = new(body), Locals = [local], ParameterLocals = [], AnalysisWarnings = [] };
        var assembly = new AssemblyDefinition("LocalInit" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        var module = new ModuleDefinition("LocalInit.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        assembly.Modules.Add(module);
        var definition = new TypeDefinition("Test", "InitializedData", TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            new TypeReference(module, module.CorLibTypeFactory.CorLibScope, "System", "ValueType"));
        module.TopLevelTypes.Add(definition); context.PutExtraData("AsmResolverType", definition);
        var numberDefinition = new FieldDefinition("Number", FieldAttributes.Public, new FieldSignature(module.CorLibTypeFactory.Int64));
        definition.Fields.Add(numberDefinition); number.PutExtraData("AsmResolverField", numberDefinition);
        if (text != null)
        {
            var textDefinition = new FieldDefinition("Text", FieldAttributes.Public, new FieldSignature(module.CorLibTypeFactory.String));
            definition.Fields.Add(textDefinition); text.PutExtraData("AsmResolverField", textDefinition);
        }
        var method = new MethodDefinition("Reset", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(definition.ToTypeSignature(true)));
        definition.Methods.Add(method); IlGenerator.GenerateIl(caller, method);
        Assert.That(method.CilMethodBody!.InitializeLocals, Is.True);
        Assert.That(method.CilMethodBody.LocalVariables.Count, Is.EqualTo(1));
        Assert.That(method.CilMethodBody.Instructions.Count(i => i.OpCode == CilOpCodes.Initobj), Is.EqualTo(1));
        using var stream = new System.IO.MemoryStream(); module.Write(stream);
        var generated = System.Reflection.Assembly.Load(stream.ToArray());
        var runtime = generated.GetType("Test.InitializedData")!;
        var value = runtime.GetMethod("Reset")!.Invoke(null, null)!;
        Assert.That(runtime.GetField("Number")!.GetValue(value), Is.EqualTo(0L));
        if (withReference) Assert.That(runtime.GetField("Text")!.GetValue(value), Is.Null);
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
