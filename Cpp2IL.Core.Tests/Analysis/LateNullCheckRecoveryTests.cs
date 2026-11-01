using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateNullCheckRecoveryTests
{
    private static IEnumerable<TestCaseData> Cases()
    {
        foreach(var targetThrows in new[]{false,true})
        foreach(var shape in new[]{"direct-void","direct-result","copy-receiver","float-argument","load","store",
            "different-receiver","effect","return-first","wrong-offset","static-field","nested-field","raw-store",
            "field-rhs","virtual-base-call","static-call","constructor","unmaterialized-argument","truncated-call",
            "unknown-receiver","value-receiver","overwrite","bounds-check","shared-success",
            "sealed-delegate","sealed-delegate-copy","unsealed-delegate","delegate-not-invoke",
            "virtual-nondelegate-sealed","delegate-other-receiver"})
            yield return new TestCaseData(shape,targetThrows,shape is "direct-void" or "direct-result" or "copy-receiver"
                or "float-argument" or "load" or "store" or "sealed-delegate" or "sealed-delegate-copy");
    }

    [TestCaseSource(nameof(Cases))]
    public void OnlyImmediateSameReceiverDereferenceRetainsTheNullException(string shape,bool targetThrows,bool expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var isDelegate=shape.Contains("delegate") && shape!="virtual-nondelegate-sealed";
        var sealedOwner=isDelegate && shape!="unsealed-delegate" || shape=="virtual-nondelegate-sealed";
        var parent=isDelegate?t.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.MulticastDelegate")!:t.SystemObjectType;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Receiver",
            parent,TypeAttributes.Public|(sealedOwner?TypeAttributes.Sealed:0));
        var field=owner.InjectFieldContext("value",t.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
        if(shape=="static-field")field.Attributes|=FieldAttributes.Static;
        var input=new LocalVariable("input",new(null,"input"),owner);
        var other=new LocalVariable("other",new(null,"other"),owner);
        var alias=new LocalVariable("alias",new(null,"alias"),owner);
        var result=new LocalVariable("result",new(null,"result"),t.SystemInt32Type);
        var condition=new LocalVariable("condition",new(null,"condition"),t.SystemBooleanType);
        var reference=new FieldReference(field,input,shape=="wrong-offset"?20:16);
        if(shape=="nested-field")reference.Parent=new FieldReference(field,other,16);
        var parameters=shape is "float-argument" or "unmaterialized-argument" or "truncated-call"
            ?new[]{shape=="float-argument"?t.SystemSingleType:t.SystemInt32Type}:System.Array.Empty<TypeAnalysisContext>();
        var target=new InjectedMethodAnalysisContext(owner,shape=="constructor"?".ctor":isDelegate && shape!="delegate-not-invoke"?"Invoke":"Read",
            shape=="direct-result"?t.SystemInt32Type:t.SystemVoidType,
            MethodAttributes.Public|(shape=="virtual-base-call" || isDelegate || shape=="virtual-nondelegate-sealed"?MethodAttributes.Virtual:0)
                |(shape=="static-call"?MethodAttributes.Static:0),parameters);
        var copied=shape is "copy-receiver" or "sealed-delegate-copy";
        var receiver=copied?alias:shape is "different-receiver" or "delegate-other-receiver"?other:input;
        Instruction operation=shape switch {
            "load" or "wrong-offset" or "static-field" or "nested-field"=>new(4,OpCode.Move,result,reference),
            "store"=>new(4,OpCode.Move,reference,new Immediate(1)),
            "field-rhs"=>new(4,OpCode.Move,reference,new FieldReference(field,other,16)),
            "raw-store"=>new(4,OpCode.Move,new MemoryOperand(input,addend:16),new Immediate(1)),
            "direct-result"=>new(4,OpCode.Call,target,result,receiver),
            _=>new(4,OpCode.CallVoid,target,receiver)};
        if(shape=="float-argument")operation.AddOperands([new FloatLiteral(1f)]);
        if(shape=="unmaterialized-argument")operation.AddOperands([new FieldReference(field,other,16)]);
        if(shape=="unknown-receiver")input.Type=null;
        if(shape=="value-receiver")input.Type=t.SystemInt32Type;
        var exception=t.SystemExceptionType.DeclaringAssembly.GetTypeByFullName(shape=="bounds-check"
            ?"System.IndexOutOfRangeException":"System.NullReferenceException")!;
        var throwing=new Instruction(7,OpCode.Throw,exception);
        var success=new List<Instruction>();
        if(copied)success.Add(new(2,OpCode.Move,alias,input));
        if(shape=="effect")success.Add(new(2,OpCode.CallVoid,new StringLiteral("observe")));
        if(shape=="return-first")success.Add(new(2,OpCode.Return));
        if(shape=="overwrite")success.Add(new(2,OpCode.Move,input,other));
        success.Add(operation);success.Add(new(5,OpCode.Return));
        var branch=new Instruction(1,OpCode.ConditionalJump,targetThrows?throwing:success[0],condition);
        var code=new List<Instruction>{new(0,targetThrows?OpCode.CheckEqual:OpCode.CheckNotEqual,condition,input,new Immediate(0)),branch};
        if(targetThrows){code.AddRange(success);code.Add(throwing);}
        else{code.Add(throwing);code.AddRange(success);}
        var graph=new ISILControlFlowGraph(code);
        if(shape=="shared-success")
        {
            var home=graph.Blocks.Single(b=>b.Instructions.Contains(operation));
            var extra=new Block{ID=99,Successors=[home]};graph.Blocks.Add(extra);home.Predecessors.Add(extra);
            graph.EntryBlock.Successors.Add(extra);extra.Predecessors.Add(graph.EntryBlock);
        }
        InjectedCheckRemover.RunNullOnly(graph);
        Assert.That(branch.OpCode,Is.EqualTo(expected?OpCode.Jump:OpCode.ConditionalJump));
        Assert.That(graph.Instructions.Contains(throwing),Is.EqualTo(!expected));
        Assert.That(operation.NativeVirtualDispatch,Is.EqualTo(expected && isDelegate));
        Assert.That(operation.NativeNullCheckedCall,Is.EqualTo(expected && target.Name=="Read" && operation.IsCall));
        Assert.That(target.IsVirtual,Is.EqualTo(shape=="virtual-base-call" || isDelegate || shape=="virtual-nondelegate-sealed"));
    }
}
