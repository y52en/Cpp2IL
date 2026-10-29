using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class OwnedDceLookupAnchorTests
{
    [TestCase("valid",true)]
    [TestCase("foreign-graph",false)]
    [TestCase("foreign-call",false)]
    [TestCase("foreign-anchor",false)]
    [TestCase("removed-call",false)]
    [TestCase("removed-anchor",false)]
    [TestCase("changed-target",false)]
    [TestCase("not-virtual",false)]
    [TestCase("changed-anchor",false)]
    [TestCase("changed-slow-target",false)]
    [TestCase("changed-slow-argument",false)]
    [TestCase("changed-slow-opcode",false)]
    [TestCase("removed-slow-call",false)]
    public void RetryRequiresAnObservedOwnedEliminationAndCurrentBindings(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.First(m=>m.IsVirtual);
        var other=owner.Methods.First(m=>!ReferenceEquals(m,target));
        var value=new LocalVariable("invoke-data",new(null,"X0"));
        var klass=new LocalVariable("klass",new(null,"X1"));
        var phi=new Instruction(-1,OpCode.Phi,value,new Immediate(0),new Immediate(1));
        var slow=new Instruction(3,OpCode.Call,new Immediate(0xA7A4D0),
            new LocalVariable("slow-result",new(null,"X2")),klass,new Immediate(0),new Immediate(0));
        var call=new Instruction(7,OpCode.CallVoid,target){NativeVirtualDispatch=true};
        var graph=new ISILControlFlowGraph([phi,slow,call,new(8,OpCode.Return)]);
        var merge=graph.Blocks.Single(b=>b.Instructions.Contains(phi));
        var match=new InterfaceDispatchRecovery.Match(target,phi,merge,slow,klass);
        var receipts=OwnedDceLookupAnchor.Eliminate(graph,[(call,match)]);
        Assert.That(receipts.Count,Is.EqualTo(1));
        Assert.That(phi.OpCode,Is.EqualTo(OpCode.Nop));
        var examinedCall=call;var examined=match;
        if(shape=="foreign-graph")graph=new ISILControlFlowGraph([new(8,OpCode.Return)]);
        if(shape=="foreign-call")examinedCall=new(7,OpCode.CallVoid,target){NativeVirtualDispatch=true};
        if(shape=="foreign-anchor")examined=match with{InvokeDataPhi=new(-1,OpCode.Nop)};
        if(shape=="removed-call")graph.Blocks.Single(b=>b.Instructions.Contains(call)).Instructions.Remove(call);
        if(shape=="removed-anchor")merge.Instructions.Remove(phi);
        if(shape=="changed-target")call.SetOperand(0,other);
        if(shape=="not-virtual")call.NativeVirtualDispatch=false;
        if(shape=="changed-anchor")phi.OpCode=OpCode.Move;
        if(shape=="changed-slow-target")slow.SetOperand(0,new Immediate(1));
        if(shape=="changed-slow-argument")slow.SetOperand(4,new Immediate(1));
        if(shape=="changed-slow-opcode")slow.OpCode=OpCode.CallVoid;
        if(shape=="removed-slow-call")graph.Blocks.Single(b=>b.Instructions.Contains(slow)).Instructions.Remove(slow);
        Assert.That(receipts[0].IsCurrent(graph,examinedCall,examined),Is.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ExternalNopAndObservableAnchorNeverReceiveAReceipt(bool observable)
    {
        var app=TestGameLoader.LoadSimple2019Game();var target=app.SystemTypes.SystemObjectType.Methods.First(m=>m.IsVirtual);
        var value=new LocalVariable("invoke-data",new(null,"X0"));
        var klass=new LocalVariable("klass",new(null,"X1"));
        var phi=new Instruction(-1,OpCode.Phi,value,new Immediate(0),new Immediate(1));
        var slow=new Instruction(3,OpCode.Call,new Immediate(0xA7A4D0),
            new LocalVariable("slow-result",new(null,"X2")),klass,new Immediate(0),new Immediate(0));
        var call=new Instruction(7,OpCode.CallVoid,target){NativeVirtualDispatch=true};
        var ret=observable?new Instruction(8,OpCode.Return,value):new Instruction(8,OpCode.Return);
        var graph=new ISILControlFlowGraph([phi,slow,call,ret]);
        var merge=graph.Blocks.Single(b=>b.Instructions.Contains(phi));
        var match=new InterfaceDispatchRecovery.Match(target,phi,merge,slow,klass);
        if(!observable){phi.OpCode=OpCode.Nop;phi.SetOperands();}
        Assert.That(OwnedDceLookupAnchor.Eliminate(graph,[(call,match)]),Is.Empty);
    }
}
