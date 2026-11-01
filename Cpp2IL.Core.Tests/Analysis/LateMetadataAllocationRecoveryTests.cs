using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateMetadataAllocationRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("unknown-result-type",true)]
    [TestCase("base-result-type",true)]
    [TestCase("valid-other-block",true)]
    [TestCase("unknown-metadata",false)]
    [TestCase("wrong-type",false)]
    [TestCase("changed-slot",false)]
    [TestCase("partial-pointer",false)]
    [TestCase("read-after-allocation",false)]
    [TestCase("metadata-parameter",false)]
    [TestCase("destination-parameter",false)]
    [TestCase("reassigned-metadata",false)]
    [TestCase("reassigned-destination",false)]
    [TestCase("metadata-value-type",false)]
    [TestCase("metadata-open-type",false)]
    [TestCase("non-dominating-read",false)]
    public void OnlyExactDominatingOriginalMetadataMayReplaceAnAllocationType(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var root=app.SystemTypes.SystemObjectType;
        var owner=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","Allocated",root,TypeAttributes.Public);
        var other=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","Other",root,TypeAttributes.Public);
        var pointer=new LocalVariable("pointer",new(null,"X22"));
        var metadata=new LocalVariable("metadata",new(null,"X0"));
        var destination=new LocalVariable("destination",new(null,"X1"),shape=="unknown-result-type"?null:shape=="base-result-type"?root:owner);
        var one=new Instruction(0,OpCode.Move,pointer,new MemoryOperand(addend:0x1000)){NativeReadSize=8};
        var two=new Instruction(1,OpCode.Move,pointer,new MemoryOperand(addend:shape=="changed-slot"?0x1100:0x1000)){NativeReadSize=8};
        var read=new Instruction(2,OpCode.Move,metadata,new MemoryOperand(pointer)){NativeReadSize=shape=="partial-pointer"?4:8};
        var allocation=new Instruction(3,OpCode.Newobj,destination,metadata);
        var instructions=new System.Collections.Generic.List<Instruction>{one,read,allocation,two,new(4,OpCode.Return,destination)};
        if(shape=="valid-other-block")instructions=[one,read,new(5,OpCode.Jump,allocation),allocation,two,instructions[^1]];
        if(shape=="read-after-allocation")instructions=[one,allocation,read,two,instructions[^1]];
        if(shape=="non-dominating-read")
        {
            instructions=[one,new(6,OpCode.ConditionalJump,allocation,new LocalVariable("condition",new(null,"flag"))),
                read,new(7,OpCode.Jump,allocation),allocation,two,instructions[^1]];
        }
        if(shape=="reassigned-metadata")instructions.Insert(3,new(5,OpCode.Move,metadata,new Immediate(0)));
        if(shape=="reassigned-destination")instructions.Insert(3,new(5,OpCode.Move,destination,new Immediate(0)));
        var method=owner.InjectMethodContext("Caller",owner,MethodAttributes.Public|MethodAttributes.Static);
        method.ControlFlowGraph=new(instructions);
        if(shape=="metadata-parameter")method.ParameterLocals.Add(metadata);
        if(shape=="destination-parameter")method.ParameterLocals.Add(destination);
        var before=method.ControlFlowGraph.Instructions.ToArray();
        TypeAnalysisContext? native=shape switch {
            "unknown-metadata"=>null,"wrong-type"=>other,"metadata-value-type"=>app.SystemTypes.SystemInt32Type,
            "metadata-open-type"=>root.DeclaringAssembly.GetTypeByFullName("System.Collections.Generic.List`1"),_=>owner};
        if(shape=="metadata-open-type")
        {
            Assert.That(native,Is.Not.Null);Assert.That(native!.GenericParameters.Count,Is.GreaterThan(0));
        }
        var result=LateMetadataAllocationRecovery.Recover(method,slot=>slot==0x1000?0x2000UL:null,address=>native);
        Assert.That(result,Is.EqualTo(expected?1:0));
        Assert.That(allocation.Operands[1],Is.SameAs(expected?(IOperand)owner:metadata));
        Assert.That(destination.Type,Is.SameAs(shape=="unknown-result-type" && !expected?null:owner));
        if(!expected)Assert.That(method.ControlFlowGraph.Instructions,Is.EqualTo(before));
    }
}
