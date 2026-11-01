using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64IntegerReturnCopyTests
{
    [TestCase("valid",true)]
    [TestCase("high-observed",false)]
    [TestCase("low-observed",false)]
    [TestCase("partial-low",false)]
    [TestCase("partial-high",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("wrong-base",false)]
    [TestCase("wrong-high-register",false)]
    [TestCase("ambiguous-target",false)]
    [TestCase("intervening-effect",false)]
    public void FullMetadataTypedPairCopiesNeverUseStaleCallerRegisters(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var guid=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Guid");
        var owner=app.SystemTypes.SystemObjectType;
        var target=new InjectedMethodAnalysisContext(owner,"Make",guid,MethodAttributes.Public|MethodAttributes.Static,[]);
        app.MethodsByAddress[0xDEAD]=shape=="ambiguous-target"?[target,target]:[target];
        var caller=new InjectedMethodAnalysisContext(owner,"Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var x0=new Register(null,"X0");var x1=new Register(null,"X1");var basis=new Register(null,"X19");
        var low=new Instruction(1,OpCode.Move,new MemoryOperand(basis,addend:16),x0){NativeWriteSize=8};
        var high=new Instruction(2,OpCode.Move,new MemoryOperand(basis,addend:24),x1){NativeWriteSize=8};
        var list=new System.Collections.Generic.List<Instruction>{new(0,OpCode.Call,new Immediate(0xDEAD),x0),low,high};
        if(shape=="high-observed")list.Add(new(3,OpCode.Move,new MemoryOperand(basis,addend:40),x1){NativeWriteSize=8});
        if(shape=="low-observed")list.Add(new(3,OpCode.Move,new MemoryOperand(basis,addend:40),x0){NativeWriteSize=8});
        if(shape=="partial-low")low.NativeWriteSize=4;
        if(shape=="partial-high")high.NativeWriteSize=4;
        if(shape=="wrong-offset")high.SetOperand(0,new MemoryOperand(basis,addend:32));
        if(shape=="wrong-base")high.SetOperand(0,new MemoryOperand(new Register(null,"X20"),addend:24));
        if(shape=="wrong-high-register")high.SetOperand(1,new Register(null,"X2"));
        if(shape=="intervening-effect")list.Insert(2,new(4,OpCode.CallVoid,new Immediate(1234)));
        list.Add(new(5,OpCode.Return));caller.ControlFlowGraph=new(list);
        var before=caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(Arm64IntegerReturnCopyRecovery.Run(caller),Is.EqualTo(expected?1:0));
        if(expected){Assert.That(low.NativeWriteSize,Is.EqualTo(16));Assert.That(high.OpCode,Is.EqualTo(OpCode.Nop));}
        else Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
    }
}
