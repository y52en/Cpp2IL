using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class VirtualTailDispatchTests
{
    [TestCase(false,false,false,0,true)]
    [TestCase(false,true,false,0,true)]
    [TestCase(true,true,false,0,true)]
    [TestCase(true,false,false,0,false)]
    [TestCase(false,false,true,0,false)]
    [TestCase(false,false,false,1,false)]
    public void ExactVirtualTailDispatchDefinesFreshResultAndExplicitReturn(bool voidTarget,bool voidCaller,bool mismatch,int delta,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.First(m=>m.Definition is {slot:<ushort.MaxValue} && m.IsVoid==voidTarget && m.Parameters.Count==0);
        var resultType=voidCaller?app.SystemTypes.SystemVoidType:mismatch?app.SystemTypes.SystemStringType:voidTarget?app.SystemTypes.SystemInt32Type:target.ReturnType;
        var method=new InjectedMethodAnalysisContext(owner,"Tail",resultType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var klass=new LocalVariable("klass",new Register(null,"X8"),new RuntimeClassTypeAnalysisContext(owner,owner.DeclaringAssembly));
        var receiver=new LocalVariable("receiver",new Register(null,"X0"),owner);
        var info=new LocalVariable("info",new Register(null,"X1"));
        var pointer=new LocalVariable("pointer",new Register(null,"X2"));
        var layout=RuntimeMetadataLayout.For(new UnityVersion(2018,4,28,UnityVersionType.Final,1),8);
        var offset=layout.VTable+target.Definition!.slot*16+delta;
        var jump=new Instruction(2,OpCode.IndirectJump,pointer,receiver);
        var raw=new List<IOperand>{receiver,info,pointer};
        raw.AddRange(Enumerable.Range(3,5).Select(i=>(IOperand)new LocalVariable("arg"+i,new Register(null,"X"+i))));
        raw.AddRange(Enumerable.Range(0,8).Select(i=>(IOperand)new LocalVariable("float"+i,new Register(null,"V"+i))));
        jump.AddOperands(raw);
        method.ControlFlowGraph=new([
            new(0,OpCode.Move,pointer,new MemoryOperand(klass,addend:offset)),
            new(1,OpCode.Move,info,new MemoryOperand(klass,addend:offset+8)),jump]);
        method.Locals=new List<LocalVariable>{klass,receiver,info,pointer};method.ParameterLocals=[];method.AnalysisWarnings=[];
        Assert.That(MetadataResolver.ResolveVirtualCalls(method,layout),Is.EqualTo(expected));
        if(!expected)
        {
            Assert.That(jump.OpCode,Is.EqualTo(OpCode.IndirectJump));
            Assert.That(method.ControlFlowGraph.Instructions.Any(i=>i.OpCode==OpCode.Return),Is.False);
            return;
        }
        Assert.That(jump.Operands[0],Is.SameAs(target));
        Assert.That(jump.NativeVirtualDispatch,Is.True);
        Assert.That(jump.OpCode,Is.EqualTo(voidTarget?OpCode.CallVoid:OpCode.Call));
        Assert.That(jump.Operands.Count,Is.EqualTo(voidTarget?3:4),"raw unused registers must not escape");
        var ret=method.ControlFlowGraph.Instructions.Single(i=>i.OpCode==OpCode.Return);
        if(!voidTarget)
        {
            var result=(LocalVariable)jump.Destination!;
            Assert.That(result,Is.Not.SameAs(receiver));
            Assert.That(result.Register.Number,Is.Not.EqualTo(receiver.Register.Number));
            Assert.That(result.Type,Is.SameAs(target.ReturnType));
            Assert.That(method.Locals,Does.Contain(result));
            if(!voidCaller)Assert.That(ret.Operands.Single(),Is.SameAs(result));
        }
        if(voidCaller)Assert.That(ret.Operands.Count,Is.Zero);
        Assert.That(jump.Operands.Any(o=>o is RuntimeMethodInfoAnalysisContext),Is.True);
        Assert.That(MetadataResolver.ResolveVirtualCalls(method,layout),Is.False,"repeat must not duplicate returns");
    }
}
