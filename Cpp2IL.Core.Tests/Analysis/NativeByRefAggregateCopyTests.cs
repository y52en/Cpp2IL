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
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeByRefAggregateCopyTests
{
    private ApplicationAnalysisContext _app=null!;
    private TypeAnalysisContext _value=null!;
    [OneTimeSetUp]
    public void Load()
    {
        _app=TestGameLoader.LoadSimple2019Game();
        _value=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Matrix4x4");
    }
    private LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new(null,name),type);
    private (MethodAnalysisContext Method,Instruction Call,LocalVariable Destination,LocalVariable Source,LocalVariable Result,Instruction Before,Instruction After) Fixture(TypeAnalysisContext? type=null)
    {
        type??=_value;var reference=new ByRefTypeAnalysisContext(type);
        var method=new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType,"Copy",type,MethodAttributes.Public|MethodAttributes.Static,[reference]);
        var destination=Local("arbitrary-parameter-name",reference);destination.ParameterIndex=0;
        var source=Local("arbitrary-source",type);var result=Local("unused-pointer");
        method.Locals.AddRange([destination,source,result]);method.ParameterLocals.Add(destination);
        var size=type is GenericInstanceTypeAnalysisContext?ClosedGenericValueLayout.TryGet(type,8)!.Value.Size:TypeSizes.UnboxedSize(type,8);
        var before=new Instruction(0,OpCode.CallVoid,new Immediate(777));
        var call=new Instruction(1,OpCode.Call,new Immediate(0xA5FC30),result,destination,new AddressOf(source),new Immediate(size),Local("unused-x3"));
        var after=new Instruction(2,OpCode.CallVoid,new Immediate(888));
        method.ControlFlowGraph=new([before,call,after,new(3,OpCode.Return,source)]);
        return(method,call,destination,source,result,before,after);
    }

    [TestCase(false)] [TestCase(true)]
    public void FullCopyWritesThroughOriginalParameterAndPreservesOtherCalls(bool noPadding)
    {
        var f=Fixture();if(noPadding)f.Call.SetOperands(f.Call.Operands.Take(5).ToList());
        Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        Assert.That(f.Call.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(f.Call.Operands[0],Is.TypeOf<MemoryOperand>());
        Assert.That(((MemoryOperand)f.Call.Operands[0]).Base,Is.SameAs(f.Destination));
        Assert.That(f.Call.Operands[1],Is.SameAs(f.Source));
        Assert.That(f.Method.ControlFlowGraph!.Instructions.Contains(f.Before),Is.True);
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.After),Is.True);
        Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
        DeadCodeEliminator.Run(f.Method);
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.Call),Is.True,"Writing external ref storage is observable");
    }

    [TestCase("unreviewed")] [TestCase("wrong-address")] [TestCase("virtual")] [TestCase("callvoid")]
    [TestCase("partial")] [TestCase("oversized")] [TestCase("dynamic-size")]
    [TestCase("unknown-source")] [TestCase("different-source-type")] [TestCase("same-named-foreign-type")]
    [TestCase("non-reference-destination")] [TestCase("metadata-mismatch")]
    [TestCase("foreign-destination")] [TestCase("not-parameter")] [TestCase("wrong-ordinal")]
    [TestCase("this")] [TestCase("method-info")] [TestCase("return-buffer")]
    [TestCase("foreign-source")] [TestCase("source-this")] [TestCase("source-buffer")]
    [TestCase("missing-source-address")] [TestCase("used-result")] [TestCase("addressed-result")]
    [TestCase("redefined-result")] [TestCase("same-result")] [TestCase("duplicate-call")]
    [TestCase("memory-padding")] [TestCase("address-padding")] [TestCase("float-padding")]
    public void NoCopyIsInferredFromNamesSizesOrUnboundPointers(string shape)
    {
        var f=Fixture();var graph=f.Method.ControlFlowGraph!;var block=graph.Blocks.Single(b=>b.Instructions.Contains(f.Call));
        switch(shape)
        {
            case "wrong-address":f.Call.SetOperand(0,new Immediate(0xA5FC34));break;
            case "virtual":f.Call.NativeVirtualDispatch=true;break;
            case "callvoid":f.Call.OpCode=OpCode.CallVoid;break;
            case "partial":f.Call.SetOperand(4,new Immediate(60));break;
            case "oversized":f.Call.SetOperand(4,new Immediate(68));break;
            case "dynamic-size":f.Call.SetOperand(4,Local("size"));break;
            case "unknown-source":f.Source.Type=null;break;
            case "different-source-type":f.Source.Type=_app.SystemTypes.SystemInt32Type;break;
            case "same-named-foreign-type":f.Source.Type=new InjectedTypeAnalysisContext(_value.DeclaringAssembly,"UnityEngine","Matrix4x4",_app.SystemTypes.SystemValueTypeType,TypeAttributes.Public);break;
            case "non-reference-destination":f.Destination.Type=_value;break;
            case "metadata-mismatch":f.Destination.Type=new ByRefTypeAnalysisContext(_app.SystemTypes.SystemInt32Type);break;
            case "foreign-destination":f.Method.Locals.Remove(f.Destination);break;
            case "not-parameter":f.Method.ParameterLocals.Clear();break;
            case "wrong-ordinal":f.Destination.ParameterIndex=1;break;
            case "this":f.Destination.IsThis=true;break;
            case "method-info":f.Destination.IsMethodInfo=true;break;
            case "return-buffer":f.Destination.IsReturnBuffer=true;break;
            case "foreign-source":f.Method.Locals.Remove(f.Source);break;
            case "source-this":f.Source.IsThis=true;break;
            case "source-buffer":f.Source.IsReturnBuffer=true;break;
            case "missing-source-address":f.Call.SetOperand(3,f.Source);break;
            case "used-result":block.Instructions.Add(new(4,OpCode.CallVoid,new Immediate(999),f.Result));break;
            case "addressed-result":block.Instructions.Add(new(4,OpCode.CallVoid,new Immediate(999),new AddressOf(f.Result)));break;
            case "redefined-result":block.Instructions.Insert(0,new(-1,OpCode.Move,f.Result,new Immediate(0)));break;
            case "same-result":f.Call.SetOperand(1,f.Source);break;
            case "duplicate-call":block.Instructions.Add(f.Call);break;
            case "memory-padding":f.Call.SetOperand(5,new MemoryOperand(f.Source));break;
            case "address-padding":f.Call.SetOperand(5,new AddressOf(f.Source));break;
            case "float-padding":f.Call.SetOperand(5,new FloatLiteral(1f));break;
        }
        var operands=f.Call.Operands.ToArray();var opcode=f.Call.OpCode;
        Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,shape!="unreviewed"),Is.False);
        Assert.That(f.Call.OpCode,Is.EqualTo(opcode));Assert.That(f.Call.Operands,Is.EqualTo(operands));
    }

    [Test]
    public void ExactClosedGenericCopyIsSupported()
    {
        var definition=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Nullable`1");
        var f=Fixture(new GenericInstanceTypeAnalysisContext(definition,[_app.SystemTypes.SystemInt32Type]));
        Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
    }

    [Test]
    public void ScalarStorageIsNotTreatedAsAnAggregate()
    {
        var f=Fixture(_app.SystemTypes.SystemInt32Type);
        Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
    }

    [Test]
    public void ProductionRejectsTheUnrelatedTestGameImage()
    {
        var f=Fixture();Assert.That(NativeByRefAggregateCopyRecovery.Run(f.Method),Is.Zero);
        Assert.That(f.Call.OpCode,Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void RecoveredStoreEmitsStobjAndUpdatesTheActualRefArgumentAtRuntime()
    {
        var guid=_app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.Guid")!;
        var f=Fixture(guid);Assert.That(NativeByRefAggregateCopyRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        var runtime=ModuleDefinition.FromFile(typeof(Guid).Assembly.Location);
        guid.PutExtraData("AsmResolverType",runtime.GetAllTypes().Single(t=>t.FullName=="System.Guid"));
        var assembly=new AssemblyDefinition("RecoveredCopy"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("RecoveredCopy.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var type=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var signature=guid.ToTypeSignature();
        var method=new MethodDefinition("Copy",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(signature,[new ByReferenceTypeSignature(signature),signature]));type.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody {InitializeLocals=true};
        var source=new CilLocalVariable(signature);var read=new CilLocalVariable(signature);method.CilMethodBody.LocalVariables.Add(source);method.CilMethodBody.LocalVariables.Add(read);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1);method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,source);
        var result=Local("read",guid);var locals=new Dictionary<LocalVariable,CilLocalVariable>{[f.Source]=source,[result]=read};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in new Instruction[]{f.Call,new(5,OpCode.Move,result,new MemoryOperand(f.Destination)),new(6,OpCode.Return,result)})
            emit.Invoke(null,[instruction,f.Method,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Count(i=>i.OpCode==CilOpCodes.Stobj),Is.EqualTo(1));
        using var stream=new MemoryStream();module.Write(stream);
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Copy")!;
        var value=Guid.Parse("12345678-1234-5678-1234-567812345678");object[] arguments=[Guid.Empty,value];
        // Only this freshly emitted fixture executes; original game assemblies supply metadata.
        Assert.That(generated.Invoke(null,arguments),Is.EqualTo(value));Assert.That(arguments[0],Is.EqualTo(value));
    }
}
