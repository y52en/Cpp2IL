using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfacePendingIdentityTests
{
    [TestCase("valid",true)]
    [TestCase("removed-call",false)]
    [TestCase("removed-phi",false)]
    [TestCase("foreign-graph",false)]
    [TestCase("same-index-foreign-call",false)]
    [TestCase("same-index-foreign-phi",false)]
    [TestCase("different-target",false)]
    [TestCase("not-virtual",false)]
    [TestCase("not-call",false)]
    [TestCase("not-phi",false)]
    public void RetryRequiresOriginalLiveInstructionIdentities(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.First(m=>m.IsVirtual);
        var other=owner.Methods.First(m=>!ReferenceEquals(m,target));
        var value=new LocalVariable("invoke-data",new(null,"X0"));
        var phi=new Instruction(-1,OpCode.Phi,value,new Immediate(0),new Immediate(1));
        var call=new Instruction(7,OpCode.CallVoid,target){NativeVirtualDispatch=true};
        var graph=new ISILControlFlowGraph([phi,call,new(8,OpCode.Return)]);
        var examinedCall=call;var examinedPhi=phi;
        if(shape=="removed-call")graph.Blocks.Single(b=>b.Instructions.Contains(call)).Instructions.Remove(call);
        if(shape=="removed-phi")graph.Blocks.Single(b=>b.Instructions.Contains(phi)).Instructions.Remove(phi);
        if(shape=="foreign-graph")graph=new ISILControlFlowGraph([new(8,OpCode.Return)]);
        if(shape=="same-index-foreign-call")examinedCall=new(7,OpCode.CallVoid,target){NativeVirtualDispatch=true};
        if(shape=="same-index-foreign-phi")examinedPhi=new(-1,OpCode.Phi,value,new Immediate(0),new Immediate(1));
        if(shape=="different-target")call.SetOperand(0,other);
        if(shape=="not-virtual")call.NativeVirtualDispatch=false;
        if(shape=="not-call")call.OpCode=OpCode.Move;
        if(shape=="not-phi")phi.OpCode=OpCode.Move;
        Assert.That(InterfaceDispatchRecovery.IsCurrentResolvedLookup(graph,examinedCall,examinedPhi,target),Is.EqualTo(expected));
    }
}
