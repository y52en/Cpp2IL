using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeArrayBoundsRecoveryTests
{
    [TestCase("compound",true)] [TestCase("compound-swapped",true)]
    [TestCase("direct",true)] [TestCase("inverted-direct",true)]
    [TestCase("address",true)] [TestCase("store",true)]
    [TestCase("wrong-factory",false)] [TestCase("wrong-array",false)]
    [TestCase("wrong-index",false)] [TestCase("signed",false)]
    [TestCase("wide-length",false)] [TestCase("wrong-subtract-index",false)]
    [TestCase("missing-equality",false)] [TestCase("wrong-polarity",false)]
    [TestCase("effect-before-test",false)] [TestCase("effect-before-access",false)]
    [TestCase("extra-failure-effect",false)] [TestCase("custom-exception",false)]
    [TestCase("shared-failure",false)] [TestCase("escaping-exception",false)]
    [TestCase("reassigned-array",false)] [TestCase("reassigned-index",false)]
    [TestCase("unknown-index",false)] [TestCase("wide-subtract",false)]
    [TestCase("unknown-subtract",false)] [TestCase("nonboolean-condition",false)]
    [TestCase("future-equality",false)] [TestCase("external-equality",false)]
    [TestCase("copied-condition",true)]
    [TestCase("live-length",true)]
    [TestCase("primitive-conversion",true)] [TestCase("object-conversion",false)]
    [TestCase("unknown-conversion",false)]
    [TestCase("zero-equal",true)] [TestCase("zero-not-equal",true)]
    [TestCase("zero-swapped",true)] [TestCase("zero-return",true)]
    [TestCase("zero-index-one",false)] [TestCase("zero-test-one",false)]
    [TestCase("zero-other-array",false)] [TestCase("zero-wide-length",false)]
    [TestCase("zero-effect-before-access",false)] [TestCase("zero-wrong-polarity",false)]
    [TestCase("reference-null",true)] [TestCase("reference-parameter",false)]
    [TestCase("fresh-object-string",true)] [TestCase("fresh-object-object",true)]
    [TestCase("fresh-string-string",false)] [TestCase("fresh-object-unknown-value",false)]
    [TestCase("fresh-object-value",false)] [TestCase("fresh-object-escaped",false)]
    [TestCase("fresh-object-duplicate-def",false)] [TestCase("fresh-object-after-length",false)]
    [TestCase("fresh-object-wrong-allocator",false)] [TestCase("fresh-object-no-allocation",false)]
    [TestCase("fresh-object-byref-call",false)]
    public void OnlySameUnsignedArrayRangeAndAutomaticFailureCanBeImplicit(string shape,bool expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        LocalVariable Local(string name,TypeAnalysisContext type)=>new(name,new(null,name),type);
        var referenceCase=shape.StartsWith("reference-",System.StringComparison.Ordinal) || shape.StartsWith("fresh-",System.StringComparison.Ordinal);
        var fresh=shape.StartsWith("fresh-",System.StringComparison.Ordinal);
        var array=Local("array",new SzArrayTypeAnalysisContext(referenceCase
            ?shape=="fresh-string-string"?t.SystemStringType:t.SystemObjectType:t.SystemInt32Type));
        var other=Local("other",array.Type!);var index=Local("index",t.SystemInt32Type);var otherIndex=Local("otherIndex",t.SystemInt32Type);
        var length=Local("length",t.SystemInt32Type);var lower=Local("lower",t.SystemBooleanType);
        var lowerNot=Local("lowerNot",t.SystemBooleanType);var difference=Local("difference",t.SystemInt32Type);
        var equal=Local("equal",t.SystemBooleanType);var unequal=Local("unequal",t.SystemBooleanType);var condition=Local("condition",t.SystemBooleanType);
        var exceptionType=t.SystemExceptionType.DeclaringAssembly.GetTypeByFullName("System.IndexOutOfRangeException")!;
        var exception=Local("exception",exceptionType);var result=Local("result",t.SystemInt32Type);
        var graph=new ISILControlFlowGraph([]);var guard=new Block{ID=2};var failure=new Block{ID=3};var success=new Block{ID=4};
        graph.Blocks=[graph.EntryBlock,guard,failure,success,graph.ExitBlock];
        foreach(var block in graph.Blocks){block.Predecessors=[];block.Successors=[];}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,failure);Edge(guard,success);Edge(failure,graph.ExitBlock);Edge(success,graph.ExitBlock);
        var load=new Instruction(0,OpCode.Move,length,new ArrayLength(shape=="wrong-array"?other:array)){NativeReadSize=shape=="wide-length"?8:4};
        var compare=new Instruction(1,OpCode.CheckLess,lower,length,index){UnsignedComparison=shape!="signed"};
        var subtract=new Instruction(3,OpCode.Subtract,difference,length,shape=="wrong-subtract-index"?otherIndex:index)
            {NativeArithmeticSize=shape=="wide-subtract"?8:shape=="unknown-subtract"?0:4};
        var join=new Instruction(6,OpCode.And,condition,shape=="compound-swapped"?unequal:lowerNot,
            shape=="compound-swapped"?lowerNot:unequal);
        var branch=new Instruction(7,OpCode.ConditionalJump,success,condition);
        guard.Instructions=[load,compare,new(2,OpCode.Not,lowerNot,lower),subtract,
            new(4,OpCode.CheckEqual,equal,difference,new Immediate(0)),new(5,OpCode.Not,unequal,equal),join,branch];
        if(shape is "direct" or "inverted-direct")
        {
            compare.SetOperands(lower,index,length);
            branch.SetOperand(1,lower);
            guard.Instructions=[load,compare,branch];
            if(shape=="inverted-direct")
            {
                guard.Instructions.Insert(2,new(2,OpCode.Not,lowerNot,lower));branch.SetOperand(0,failure);branch.SetOperand(1,lowerNot);
            }
        }
        var allocation=new Instruction(8,OpCode.Newobj,exception,shape=="custom-exception"?t.SystemExceptionType:exceptionType)
            {NativeDirectCallTarget=shape=="wrong-factory"?0xaae404u:0xaae400u};
        failure.Instructions=[allocation,new(9,OpCode.Throw,exception)];
        var access=new ArrayAccess(array,shape=="wrong-index"?otherIndex:index);
        if(shape.StartsWith("zero-",System.StringComparison.Ordinal) || referenceCase)
        {
            access=new ArrayAccess(array,new Immediate(shape=="zero-index-one"?1:0));
            compare.OpCode=shape=="zero-not-equal"?OpCode.CheckNotEqual:OpCode.CheckEqual;
            compare.UnsignedComparison=false;
            compare.SetOperands(lower,shape=="zero-swapped"?new Immediate(0):length,
                shape=="zero-swapped"?length:new Immediate(shape=="zero-test-one"?1:0));
            branch.SetOperands(shape=="zero-not-equal"?success:failure,lower);
            guard.Instructions=[load,compare,branch];
            if(shape=="zero-other-array")load.SetOperand(1,new ArrayLength(other));
            if(shape=="zero-wide-length")load.NativeReadSize=8;
            if(shape=="zero-wrong-polarity")branch.SetOperand(0,success);
        }
        var operation=shape=="address"?new Instruction(10,OpCode.Move,Local("address",new ByRefTypeAnalysisContext(t.SystemInt32Type)),new AddressOf(access))
            :shape=="store"?new Instruction(10,OpCode.Move,access,new Immediate(12)):new Instruction(10,OpCode.Move,result,access);
        success.Instructions=[operation,new(11,OpCode.Return)];
        if(referenceCase)
        {
            IOperand stored=shape=="reference-null"?new Immediate(0):
                Local("stored",shape=="fresh-object-object"?t.SystemObjectType:shape=="fresh-object-value"?t.SystemInt32Type:t.SystemStringType);
            if(shape=="fresh-object-unknown-value")((LocalVariable)stored).Type=null;
            operation=new Instruction(10,OpCode.Move,access,stored);
            success.Instructions=[operation,new(11,OpCode.Return)];
            if(fresh && shape!="fresh-object-no-allocation")
            {
                var allocationType=shape=="fresh-object-wrong-allocator"?new SzArrayTypeAnalysisContext(t.SystemStringType):array.Type!;
                var arrayAllocation=new Instruction(30,OpCode.NewArr,array,allocationType,new Immediate(1));
                graph.EntryBlock.Instructions=[arrayAllocation];
                if(shape=="fresh-object-after-length")
                {graph.EntryBlock.Instructions=[];guard.Instructions.Insert(1,arrayAllocation);}
                if(shape=="fresh-object-duplicate-def")guard.Instructions.Insert(0,new(31,OpCode.Move,array,other));
                if(shape=="fresh-object-escaped")guard.Instructions.Insert(0,new(31,OpCode.CallVoid,new StringLiteral("escape"),new AddressOf(array)));
                if(shape=="fresh-object-byref-call")
                {
                    var borrow=new InjectedMethodAnalysisContext(t.SystemObjectType,"Borrow",t.SystemVoidType,MethodAttributes.Static,
                        [new ByRefTypeAnalysisContext(array.Type!)]);
                    guard.Instructions.Insert(0,new(31,OpCode.CallVoid,borrow,array));
                }
            }
        }
        if(shape=="zero-return")
        {
            operation=new Instruction(10,OpCode.Return,access);
            success.Instructions=[operation];
        }
        if(shape=="zero-effect-before-access")success.Instructions.Insert(0,new(20,OpCode.CallVoid,new StringLiteral("observe")));
        if(shape=="live-length")success.Instructions[1]=new(11,OpCode.Return,length);
        if(shape is "primitive-conversion" or "object-conversion" or "unknown-conversion")
        {
            var from=shape=="object-conversion"?t.SystemObjectType:t.SystemSingleType;
            var input=Local("convertInput",from);var converted=Local("convertOutput",t.SystemInt32Type);
            if(shape=="unknown-conversion")input.Type=null;
            success.Instructions.Insert(0,new(22,OpCode.NumericConvert,converted,t.SystemInt32Type,from,input));
        }
        if(shape=="effect-before-test")guard.Instructions.Insert(1,new(20,OpCode.CallVoid,new StringLiteral("observe")));
        if(shape=="effect-before-access")success.Instructions.Insert(0,new(20,OpCode.CallVoid,new StringLiteral("observe")));
        if(shape=="extra-failure-effect")failure.Instructions.Insert(1,new(20,OpCode.CallVoid,new StringLiteral("observe")));
        if(shape=="missing-equality")branch.SetOperand(1,lowerNot);
        if(shape=="wrong-polarity")branch.SetOperand(0,failure);
        if(shape=="shared-failure")Edge(graph.EntryBlock,failure);
        if(shape=="escaping-exception")success.Instructions.Add(new(20,OpCode.CallVoid,new StringLiteral("observe"),exception));
        if(shape=="reassigned-array")guard.Instructions.Insert(0,new(20,OpCode.Move,array,other));
        if(shape=="reassigned-index")guard.Instructions.Insert(0,new(20,OpCode.Move,index,otherIndex));
        if(shape=="unknown-index")index.Type=null;
        if(shape=="nonboolean-condition")condition.Type=t.SystemInt32Type;
        if(shape=="future-equality")
        {
            var equality=guard.Instructions[4];guard.Instructions.Remove(equality);
            guard.Instructions.Insert(7,equality);
        }
        if(shape=="external-equality")
        {
            var equality=guard.Instructions[4];guard.Instructions.Remove(equality);
            graph.EntryBlock.Instructions=[equality];
        }
        if(shape=="copied-condition")
        {
            var copy=Local("conditionCopy",t.SystemBooleanType);
            guard.Instructions.Insert(7,new(21,OpCode.Move,copy,condition));branch.SetOperand(1,copy);
        }
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Test",t.SystemVoidType,MethodAttributes.Static,[])
            {ControlFlowGraph=graph,ParameterLocals=[array,other,index,otherIndex]};
        if(fresh)method.ParameterLocals.Remove(array);
        foreach(var block in graph.Blocks)block.CalculateBlockType();
        var before=graph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(NativeArrayBoundsRecovery.TryRecover(method,guard,i=>i.NativeDirectCallTarget==0xaae400),Is.EqualTo(expected));
        if(!expected)Assert.That(graph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
        else
        {
            Assert.That(branch.OpCode,Is.EqualTo(OpCode.Jump));Assert.That(branch.Operands[0],Is.SameAs(success));
            graph.RemoveUnreachableBlocks();DeadCodeEliminator.Run(graph);
            Assert.That(graph.Instructions.Contains(allocation),Is.False);
            Assert.That(operation.OpCode,Is.EqualTo(shape=="zero-return"?OpCode.Return:OpCode.Move),"Implicit null/bounds exceptions remain even with an unused result");
            Assert.That(load.OpCode,Is.EqualTo(shape=="live-length"?OpCode.Move:OpCode.Nop),
                "Only an unused proven length is redundant with the next managed access");
        }
    }
}
