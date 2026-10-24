using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class PrimitiveByRefStorageRecoveryTests
{
    [TestCase("System.Int32",37)] [TestCase("System.Single",3.5f)] [TestCase("System.Boolean",true)]
    public void RecoveredPrimitivePointerCopyEmitsNoPrivateFieldAndExecutes(string name,object input)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=app.SystemTypes.SystemInt32Type.DeclaringAssembly.GetTypeByFullName(name)!;
        var field=owner.Fields.Single(f=>!f.IsStatic);var width=(int)TypeSizes.UnboxedSize(owner,app.Binary.PointerSizeBytes);
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Copy",owner,MethodAttributes.Public|MethodAttributes.Static,[]);
        var source=new LocalVariable("source",new(null,"source"),owner);
        var pointer=new LocalVariable("pointer",new(null,"pointer"),new ByRefTypeAnalysisContext(owner));
        var read=new LocalVariable("read",new(null,"read"),owner);
        context.ControlFlowGraph=new([new(0,OpCode.Move,new FieldReference(field,pointer,0),source){NativeWriteSize=width},
            new(1,OpCode.Move,read,new FieldReference(field,pointer,0)){NativeReadSize=width},new(2,OpCode.Return,read)]);
        Assert.That(PrimitiveByRefStorageRecovery.Recover(context),Is.EqualTo(2));
        var assembly=new AsmResolver.DotNet.AssemblyDefinition("PrimitivePointer"+System.Guid.NewGuid().ToString("N"),new System.Version(1,0));
        var module=new AsmResolver.DotNet.ModuleDefinition("PrimitivePointer.dll",new AsmResolver.DotNet.AssemblyReference("mscorlib",new System.Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var type=new AsmResolver.DotNet.TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var signature=name switch {"System.Single"=>module.CorLibTypeFactory.Single,
            "System.Boolean"=>module.CorLibTypeFactory.Boolean,_=>module.CorLibTypeFactory.Int32};
        // Normal production emission already exports the type table. This
        // detached fixture binds only the real runtime primitive definition.
        var runtimeModule=AsmResolver.DotNet.ModuleDefinition.FromFile(typeof(int).Assembly.Location);
        owner.PutExtraData("AsmResolverType",runtimeModule.GetAllTypes().Single(t=>t.FullName==name));
        var method=new AsmResolver.DotNet.MethodDefinition("Copy",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            AsmResolver.DotNet.Signatures.MethodSignature.CreateStatic(signature,[signature]));
        type.Methods.Add(method);method.CilMethodBody=new AsmResolver.DotNet.Code.Cil.CilMethodBody{InitializeLocals=true};
        var sourceLocal=new AsmResolver.DotNet.Code.Cil.CilLocalVariable(signature);
        var targetLocal=new AsmResolver.DotNet.Code.Cil.CilLocalVariable(signature);
        var pointerLocal=new AsmResolver.DotNet.Code.Cil.CilLocalVariable(new AsmResolver.DotNet.Signatures.ByReferenceTypeSignature(signature));
        var readLocal=new AsmResolver.DotNet.Code.Cil.CilLocalVariable(signature);
        foreach(var local in new[]{sourceLocal,targetLocal,pointerLocal,readLocal})method.CilMethodBody.LocalVariables.Add(local);
        var il=method.CilMethodBody.Instructions;
        il.Add(AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldarg_0);
        il.Add(AsmResolver.PE.DotNet.Cil.CilOpCodes.Stloc,sourceLocal);
        il.Add(AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldloca,targetLocal);
        il.Add(AsmResolver.PE.DotNet.Cil.CilOpCodes.Stloc,pointerLocal);
        var locals=new System.Collections.Generic.Dictionary<LocalVariable,AsmResolver.DotNet.Code.Cil.CilLocalVariable>
            {[source]=sourceLocal,[pointer]=pointerLocal,[read]=readLocal};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in context.ControlFlowGraph.Instructions)emit.Invoke(null,[instruction,context,method,locals,method]);
        Assert.That(il.Count(i=>i.OpCode==AsmResolver.PE.DotNet.Cil.CilOpCodes.Stobj),Is.EqualTo(1));
        Assert.That(il.Count(i=>i.OpCode==AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldobj),Is.EqualTo(1));
        Assert.That(il.Any(i=>i.OpCode==AsmResolver.PE.DotNet.Cil.CilOpCodes.Stfld || i.OpCode==AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldfld),Is.False);
        using var stream=new System.IO.MemoryStream();module.Write(stream);
        // Execute only this freshly generated fixture, not original game code.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Copy")!;
        Assert.That(generated.Invoke(null,[input]),Is.EqualTo(input));
    }

    [TestCase("System.Boolean")] [TestCase("System.Byte")] [TestCase("System.SByte")]
    [TestCase("System.Char")] [TestCase("System.Int16")] [TestCase("System.UInt16")]
    [TestCase("System.Int32")] [TestCase("System.UInt32")] [TestCase("System.Int64")]
    [TestCase("System.UInt64")] [TestCase("System.Single")] [TestCase("System.Double")]
    public void WholePrimitiveStorageReadAndWriteKeepManagedPointer(string name)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=app.SystemTypes.SystemInt32Type.DeclaringAssembly.GetTypeByFullName(name)!;
        var field=owner.Fields.Single(f=>!f.IsStatic);
        var pointer=new LocalVariable("pointer",new(null,"X0"),new ByRefTypeAnalysisContext(owner));
        var result=new LocalVariable("result",new(null,"X1"),owner);
        var target=new FieldReference(field,pointer,0);
        var width=(int)TypeSizes.UnboxedSize(owner,app.Binary.PointerSizeBytes);
        var write=new Instruction(0,OpCode.Move,target,result){NativeWriteSize=width};
        var read=new Instruction(1,OpCode.Move,result,target){NativeReadSize=width};
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Test",owner,MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([write,read,new(2,OpCode.Return,result)]);
        Assert.That(PrimitiveByRefStorageRecovery.Recover(method),Is.EqualTo(2));
        Assert.That(write.Operands[0],Is.TypeOf<MemoryOperand>());
        Assert.That(read.Operands[1],Is.TypeOf<MemoryOperand>());
        Assert.That(((MemoryOperand)write.Operands[0]).Base,Is.SameAs(pointer));
        Assert.That(((MemoryOperand)read.Operands[1]).Base,Is.SameAs(pointer));
    }

    [TestCase("partial")] [TestCase("wide")] [TestCase("unknown-width")]
    [TestCase("wrong-owner")] [TestCase("not-byref")] [TestCase("offset")]
    [TestCase("parent")] [TestCase("injected-field")] [TestCase("address-of")]
    public void PartialUnownedOrAddressOperationsRemainUnchanged(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();var owner=app.SystemTypes.SystemInt32Type;
        var field=owner.Fields.Single(f=>!f.IsStatic);
        if(shape=="injected-field")field=new InjectedFieldAnalysisContext("m_value",owner,FieldAttributes.Private,owner,0);
        var pointer=new LocalVariable("pointer",new(null,"X0"),shape=="not-byref"?owner:
            new ByRefTypeAnalysisContext(shape=="wrong-owner"?app.SystemTypes.SystemSingleType:owner));
        var value=new LocalVariable("value",new(null,"W1"),owner);
        var reference=new FieldReference(field,pointer,shape=="offset"?4:0);
        if(shape=="parent")reference.Parent=new FieldReference(field,pointer,0);
        var write=new Instruction(0,OpCode.Move,shape=="address-of"?new AddressOf(reference):reference,value)
            {NativeWriteSize=shape=="partial"?1:shape=="wide"?8:shape=="unknown-width"?0:4};
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Test",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([write,new(1,OpCode.Return)]);
        var before=write.ToString();
        Assert.That(PrimitiveByRefStorageRecovery.Recover(method),Is.Zero);
        Assert.That(write.ToString(),Is.EqualTo(before));
    }
}
