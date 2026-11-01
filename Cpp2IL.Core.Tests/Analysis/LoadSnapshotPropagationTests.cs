using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LoadSnapshotPropagationTests
{
    private static LocalVariable Local(string n)=>new(n,new Register(null,n));
    private static MethodAnalysisContext Method(ISILControlFlowGraph graph,params LocalVariable[] locals)
    {
        var method=(MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph=graph;method.Locals=locals.ToList();method.ParameterLocals=[];
        return method;
    }

    [TestCase("call")]
    [TestCase("write")]
    [TestCase("possible_exception")]
    public void PostSsaMemoryReadIsASnapshotNotALaterReload(string shape)
    {
        var pointer=Local("pointer");var saved=Local("saved");
        var load=new Instruction(0,OpCode.Move,saved,new MemoryOperand(pointer,addend:16)){NativeReadSize=4};
        var effect=shape=="write" ? new Instruction(1,OpCode.Move,new MemoryOperand(pointer,addend:16),new Immediate(9))
            : new Instruction(1,OpCode.CallVoid,new StringLiteral(shape));
        var ret=new Instruction(2,OpCode.Return,saved);
        var graph=new ISILControlFlowGraph([load,effect,ret]);
        Simplifier.Simplify(Method(graph,pointer,saved));
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(ret.Operands[0],Is.SameAs(saved));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void SsaArrayReadCannotMovePastEffectsOrDuplicateChecks(bool length)
    {
        var array=Local("array");var saved=Local("saved");
        IOperand source=length ? new ArrayLength(array) : new ArrayAccess(array,new Immediate(0));
        var load=new Instruction(0,OpCode.Move,saved,source);
        var ret=new Instruction(2,OpCode.Return,saved);
        var graph=new ISILControlFlowGraph([load,new(1,OpCode.CallVoid,new StringLiteral("effect")),ret]);
        SsaSimplifier.Run(graph,[]);
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(ret.Operands[0],Is.SameAs(saved));
    }

    [Test]
    public void AdjacentFirstUseDoesNotAuthorizeDuplicatingALoadAtAnotherUse()
    {
        var pointer=Local("pointer");var saved=Local("saved");
        var load=new Instruction(0,OpCode.Move,saved,new MemoryOperand(pointer));
        var call=new Instruction(1,OpCode.CallVoid,new StringLiteral("mutate"),saved);
        var ret=new Instruction(2,OpCode.Return,saved);
        var graph=new ISILControlFlowGraph([load,call,ret]);
        Simplifier.Simplify(Method(graph,pointer,saved));
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(call.Operands[1],Is.SameAs(saved));
        Assert.That(ret.Operands[0],Is.SameAs(saved));
    }
}
