using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeMemoryBarrierRecoveryTests
{
    [TestCase("bf3b03d5c0035fd6",true)]
    [TestCase("",false)] [TestCase("bf3b03d5",false)]
    [TestCase("bf3b03d5c0035fd61f2003d5",false)]
    [TestCase("bf3a03d5c0035fd6",false)] // ISHST is NOT the reviewed full barrier.
    [TestCase("df3f03d5c0035fd6",false)]
    [TestCase("1f2003d5c0035fd6",false)]
    [TestCase("bf3b03d500000000",false)]
    public void OnlyTheCompleteOriginalDmbIshReturnMatches(string hex,bool expected)
        =>Assert.That(NativeMemoryBarrierRecovery.Matches(Convert.FromHexString(hex)),Is.EqualTo(expected));

    [TestCase("call",1)] [TestCase("void-call",1)] [TestCase("two-calls",2)]
    [TestCase("wrong-proof",0)] [TestCase("wrong-address",0)] [TestCase("folded-target",0)]
    [TestCase("live-result",0)] [TestCase("nested-live-result",0)] [TestCase("redefined-result",0)]
    [TestCase("virtual",0)] [TestCase("null-call",0)] [TestCase("implicit-clobber",0)]
    [TestCase("field-argument",0)] [TestCase("address-argument",0)]
    [TestCase("wrong-owner",0)] [TestCase("wrong-name",0)] [TestCase("instance-target",0)]
    [TestCase("nonvoid-target",0)] [TestCase("parameter-target",0)] [TestCase("self-recursion",0)]
    public void PreserveTheBarrierAndEffectOrderWithoutInventingAReturnValue(string shape,int expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"System.Threading",
            shape=="wrong-owner"?"NotThread":"Thread",t.SystemObjectType,TypeAttributes.Public);
        var target=new InjectedMethodAnalysisContext(owner,shape=="wrong-name"?"Yield":"MemoryBarrier",
            shape=="nonvoid-target"?t.SystemInt32Type:t.SystemVoidType,
            MethodAttributes.Public|(shape=="instance-target"?0:MethodAttributes.Static),
            shape=="parameter-target"?[t.SystemInt32Type]:[]);
        var method=shape=="self-recursion"?target:new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",
            t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var input=new LocalVariable("input",new(null,"X0"),t.SystemObjectType);
        var result=new LocalVariable("result",new(null,"result"));
        var field=owner.InjectFieldContext("value",t.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
        var before=new Instruction(0,OpCode.CallVoid,new StringLiteral("before"));
        var after=new Instruction(2,OpCode.Move,new FieldReference(field,input,16),new Immediate(0));
        var call=shape=="void-call"?new Instruction(1,OpCode.CallVoid,new Immediate(0xaa3468),input)
            :new Instruction(1,OpCode.Call,new Immediate(0xaa3468),result,input);
        call.NativeDirectCallTarget=0xaa3468;
        var code=new List<Instruction>{before,call,after};
        if(shape=="two-calls")code.Insert(2,new Instruction(4,OpCode.Call,new Immediate(0xaa3468),
            new LocalVariable("second",new(null,"second")),result));
        if(shape=="live-result")code.Add(new(3,OpCode.Return,result));
        else if(shape=="nested-live-result")code.Add(new(3,OpCode.Move,input,new MemoryOperand(result)));
        else if(shape=="redefined-result")code.Add(new(3,OpCode.Move,result,new Immediate(1)));
        code.Add(new(5,OpCode.Return));
        if(shape=="wrong-address")call.SetOperand(0,new Immediate(0xaa346c));
        if(shape=="folded-target")call.SetOperand(0,input);
        if(shape=="virtual")call.NativeVirtualDispatch=true;
        if(shape=="null-call")call.NativeNullCheckedCall=true;
        if(shape=="implicit-clobber")call.ImplicitDefinition=new Register(null,"X1");
        if(shape=="field-argument")call.AddOperands([new FieldReference(field,input,16)]);
        if(shape=="address-argument")call.AddOperands([new AddressOf(input)]);
        var graph=new ISILControlFlowGraph(code);method.ControlFlowGraph=graph;
        var original=graph.Instructions.ToArray();
        Assert.That(NativeMemoryBarrierRecovery.Rewrite(method,target,a=>shape!="wrong-proof" && a==0xaa3468),Is.EqualTo(expected));
        Assert.That(graph.Instructions,Is.EqualTo(original),"No barrier or neighboring effect may be removed or reordered");
        if(expected>0)
        {
            Assert.That(call.OpCode,Is.EqualTo(OpCode.CallVoid));Assert.That(call.Operands.ToArray(),Is.EqualTo(new IOperand[]{target}));
            Assert.That(call.NativeDirectCallTarget,Is.Zero);
            Assert.That(graph.Instructions.Count(i=>i.IsCall && ReferenceEquals(i.Operands[0],target)),Is.EqualTo(expected));
        }
        else Assert.That(call.Operands[0],Is.Not.SameAs(target));
    }
}
