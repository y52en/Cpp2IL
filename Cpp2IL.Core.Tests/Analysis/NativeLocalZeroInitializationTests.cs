using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeLocalZeroInitializationTests
{
    private ApplicationAnalysisContext _app=null!;
    private TypeAnalysisContext _value=null!;
    [OneTimeSetUp]
    public void Load()
    {
        _app=TestGameLoader.LoadSimple2019Game();
        _value=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Matrix4x4");
        Assert.That(TypeSizes.UnboxedSize(_value,8),Is.EqualTo(64));
    }
    private LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new(null,name),type);
    private (MethodAnalysisContext Method,Instruction Call,LocalVariable Local,LocalVariable Result,Instruction Before,Instruction After) Fixture()
    {
        var method=new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType,"Caller",_value,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var local=Local("arbitrary-storage-name",_value);var result=Local("pointer-result");
        method.Locals.AddRange([local,result]);
        var before=new Instruction(0,OpCode.CallVoid,new Immediate(777));
        var call=new Instruction(1,OpCode.Call,new Immediate(0xA5FF10),result,new AddressOf(local),new Immediate(0),new Immediate(64),Local("unused-x3"));
        var after=new Instruction(2,OpCode.CallVoid,new Immediate(888),new AddressOf(local));
        method.ControlFlowGraph=new([before,call,after,new(3,OpCode.Return,local)]);
        return(method,call,local,result,before,after);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void CompleteLocalInitializationPreservesStorageEffectsAndEdges(bool noPadding)
    {
        var f=Fixture();if(noPadding)f.Call.SetOperands(f.Call.Operands.Take(5).ToList());
        var edges=f.Method.ControlFlowGraph!.Blocks.Select(b=>b.Successors.ToArray()).ToArray();
        Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        Assert.That(f.Call.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(f.Call.Operands[0],Is.SameAs(f.Local));
        Assert.That(f.Call.Operands[1],Is.EqualTo(new DefaultStructValue(_value)));
        Assert.That(f.Call.NativeZeroSize,Is.EqualTo(64));
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.Before),Is.True);
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.After),Is.True);
        for(var i=0;i<edges.Length;i++)Assert.That(f.Method.ControlFlowGraph.Blocks[i].Successors,Is.EqualTo(edges[i]));
        Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
    }

    [TestCase("unreviewed")]
    [TestCase("unknown-type")]
    [TestCase("reference-type")]
    [TestCase("scalar")]
    [TestCase("partial")]
    [TestCase("oversized")]
    [TestCase("nonzero")]
    [TestCase("dynamic-size")]
    [TestCase("dynamic-zero")]
    [TestCase("foreign-address")]
    [TestCase("virtual")]
    [TestCase("callvoid")]
    [TestCase("bad-result")]
    [TestCase("this")]
    [TestCase("return")]
    [TestCase("return-buffer")]
    [TestCase("method-info")]
    [TestCase("parameter-ordinal")]
    [TestCase("parameter-identity")]
    [TestCase("foreign-local")]
    [TestCase("raw-pointer")]
    [TestCase("read-result")]
    [TestCase("address-result")]
    [TestCase("redefined-result")]
    [TestCase("same-result")]
    [TestCase("memory-padding")]
    [TestCase("address-padding")]
    [TestCase("float-padding")]
    [TestCase("duplicate-call")]
    public void UnprovedOrPartialOperationsRemainUntouched(string shape)
    {
        var f=Fixture();var graph=f.Method.ControlFlowGraph!;var block=graph.Blocks.Single(b=>b.Instructions.Contains(f.Call));
        switch(shape)
        {
            case "unknown-type":f.Local.Type=null;break;
            case "reference-type":f.Local.Type=_app.SystemTypes.SystemObjectType;break;
            case "scalar":f.Local.Type=_app.SystemTypes.SystemInt32Type;f.Call.SetOperand(4,new Immediate(4));break;
            case "partial":f.Call.SetOperand(4,new Immediate(60));break;
            case "oversized":f.Call.SetOperand(4,new Immediate(68));break;
            case "nonzero":f.Call.SetOperand(3,new Immediate(1));break;
            case "dynamic-size":f.Call.SetOperand(4,Local("size"));break;
            case "dynamic-zero":f.Call.SetOperand(3,Local("zero"));break;
            case "foreign-address":f.Call.SetOperand(0,new Immediate(0xA5FF14));break;
            case "virtual":f.Call.NativeVirtualDispatch=true;break;
            case "callvoid":f.Call.OpCode=OpCode.CallVoid;break;
            case "bad-result":f.Call.SetOperand(1,new Immediate(0));break;
            case "this":f.Local.IsThis=true;break;
            case "return":f.Local.IsReturn=true;break;
            case "return-buffer":f.Local.IsReturnBuffer=true;break;
            case "method-info":f.Local.IsMethodInfo=true;break;
            case "parameter-ordinal":f.Local.ParameterIndex=0;break;
            case "parameter-identity":f.Method.ParameterLocals.Add(f.Local);break;
            case "foreign-local":f.Method.Locals.Remove(f.Local);break;
            case "raw-pointer":f.Call.SetOperand(2,f.Local);break;
            case "read-result":block.Instructions.Add(new(5,OpCode.CallVoid,new Immediate(999),f.Result));break;
            case "address-result":block.Instructions.Add(new(5,OpCode.CallVoid,new Immediate(999),new AddressOf(f.Result)));break;
            case "redefined-result":block.Instructions.Insert(0,new(-1,OpCode.Move,f.Result,new Immediate(0)));break;
            case "same-result":f.Call.SetOperand(1,f.Local);break;
            case "memory-padding":f.Call.SetOperand(5,new MemoryOperand(f.Local));break;
            case "address-padding":f.Call.SetOperand(5,new AddressOf(f.Local));break;
            case "float-padding":f.Call.SetOperand(5,new FloatLiteral(1f));break;
            case "duplicate-call":block.Instructions.Add(f.Call);break;
        }
        var operands=f.Call.Operands.ToArray();var opcode=f.Call.OpCode;
        Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,shape!="unreviewed"),Is.False);
        Assert.That(f.Call.OpCode,Is.EqualTo(opcode));Assert.That(f.Call.Operands,Is.EqualTo(operands));
    }

    [Test]
    public void ClosedNullableUsesItsExactMetadataLayout()
    {
        var f=Fixture();var definition=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Nullable`1");
        var closed=new GenericInstanceTypeAnalysisContext(definition,[_app.SystemTypes.SystemInt32Type]);
        var layout=ClosedGenericValueLayout.TryGet(closed,8);Assert.That(layout,Is.Not.Null);
        f.Local.Type=closed;f.Call.SetOperand(4,new Immediate(layout!.Value.Size));
        Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        Assert.That(f.Call.Operands[1],Is.EqualTo(new DefaultStructValue(closed)));
    }

    [Test]
    public void OpenGenericNeverUsesAnInventedSize()
    {
        var f=Fixture();f.Local.Type=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Nullable`1");
        Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
    }

    [Test]
    public void DefaultAssignmentSurvivesDceWhenLocalAddressEscapesToConsumer()
    {
        var f=Fixture();Assert.That(NativeLocalZeroInitializationRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        DeadCodeEliminator.Run(f.Method);
        Assert.That(f.Method.ControlFlowGraph!.Instructions.Contains(f.Call),Is.True);
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.Before),Is.True);
        Assert.That(f.Method.ControlFlowGraph.Instructions.Contains(f.After),Is.True);
    }

    [Test]
    public void ProductionDoesNotAcceptTheDifferentTestGameImage()
    {
        var f=Fixture();Assert.That(NativeLocalZeroInitializationRecovery.Run(f.Method),Is.Zero);
        Assert.That(f.Call.OpCode,Is.EqualTo(OpCode.Call));
    }
}
