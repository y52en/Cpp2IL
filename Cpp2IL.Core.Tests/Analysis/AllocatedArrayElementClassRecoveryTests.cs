using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class AllocatedArrayElementClassRecoveryTests
{
    [TestCase("normal",true)] [TestCase("null",true)] [TestCase("literal",true)]
    [TestCase("closed-element",true)] [TestCase("open-element",false)]
    [TestCase("parameter-array",false)] [TestCase("field-array",false)]
    [TestCase("multiple-array",false)] [TestCase("multiple-class",false)] [TestCase("multiple-element",false)]
    [TestCase("wrong-class-offset",false)] [TestCase("wrong-element-offset",false)]
    [TestCase("class-width",false)] [TestCase("element-width",false)]
    [TestCase("wrong-allocation-type",false)] [TestCase("value-element",false)]
    [TestCase("escaped-array",false)] [TestCase("escaped-class",false)] [TestCase("escaped-element",false)]
    [TestCase("late-class-load",false)] [TestCase("bypass-allocation",false)]
    [TestCase("wrong-class-type",false)] [TestCase("wrong-element-type",false)]
    [TestCase("value-source",false)] [TestCase("unknown-source",false)]
    [TestCase("wrong-helper",false)] [TestCase("wrong-target",false)] [TestCase("value-result",false)]
    public void ActualAllocationIsRequiredAndEveryGuardAndThrowIsPreserved(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var element=shape=="value-element"?types.SystemInt32Type:types.SystemStringType;
        if(shape is "closed-element" or "open-element")
        {
            var definition=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.List`1");
            element=shape=="open-element"?definition:new GenericInstanceTypeAnalysisContext(definition,[types.SystemStringType]);
        }
        var arrayType=new SzArrayTypeAnalysisContext(element);
        var array=new LocalVariable("array",new Register(null,"array"),arrayType);
        var klass=new LocalVariable("klass",new Register(null,"klass"),new RuntimeClassTypeAnalysisContext(arrayType,arrayType.DeclaringAssembly));
        var handle=new LocalVariable("element",new Register(null,"element"),null);
        var value=new LocalVariable("value",new Register(null,"value"),shape=="unknown-source"?null:
            shape=="value-source"?types.SystemInt32Type:types.SystemObjectType);
        var result=new LocalVariable("result",new Register(null,"result"),shape=="value-result"?types.SystemInt32Type:null);
        var flag=new LocalVariable("flag",new Register(null,"flag"),types.SystemBooleanType);
        var method=new InjectedMethodAnalysisContext(types.SystemObjectType,"Caller",types.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var graph=new ISILControlFlowGraph([]);method.ControlFlowGraph=graph;
        method.Locals=[array,klass,handle,value,result,flag];method.ParameterLocals=[value];method.AnalysisWarnings=[];
        var guard=new Block{ID=2};var store=new Block{ID=3};var failure=new Block{ID=4};
        graph.Blocks.AddRange([guard,store,failure]);
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,guard);Edge(guard,store);Edge(guard,failure);Edge(store,graph.ExitBlock);Edge(failure,graph.ExitBlock);
        var allocation=new Instruction(0,OpCode.NewArr,array,shape=="wrong-allocation-type"?
            new SzArrayTypeAnalysisContext(types.SystemObjectType):arrayType,new Immediate(4));
        var classLoad=new Instruction(1,OpCode.Move,klass,new MemoryOperand(array,addend:shape=="wrong-class-offset"?8:0))
            {NativeReadSize=shape=="class-width"?4:8};
        var elementLoad=new Instruction(2,OpCode.Move,handle,new MemoryOperand(klass,addend:shape=="wrong-element-offset"?72:64))
            {NativeReadSize=shape=="element-width"?4:8};
        IOperand input=shape=="null"?new Immediate(0):shape=="literal"?new StringLiteral("same reference"):value;
        var call=new Instruction(3,OpCode.Call,new StringLiteral(shape=="wrong-helper"?"unknown":"il2cpp_vm_object_is_inst"),result,input,handle)
            {NativeDirectCallTarget=shape=="wrong-target"?0xABB900UL:0xABB8FCUL};
        var comparison=new Instruction(4,OpCode.CheckEqual,flag,result,new Immediate(0));
        var branch=new Instruction(5,OpCode.ConditionalJump,failure,flag);
        guard.Instructions=[allocation,classLoad,elementLoad,call,comparison,branch];
        var write=new Instruction(6,OpCode.Move,new ArrayAccess(array,new Immediate(0)),input);
        store.Instructions=[write,new(7,OpCode.Return)];
        // This sentinel models the preexisting failure transport. The rewrite
        // may change neither the exception operand nor the path reaching it.
        var thrown=new StringLiteral("original failure transport");var throwInstruction=new Instruction(8,OpCode.Throw,thrown);
        failure.Instructions=[throwInstruction];
        if(shape=="parameter-array"){guard.Instructions.Remove(allocation);method.ParameterLocals.Add(array);}
        if(shape=="field-array")
        {
            allocation.OpCode=OpCode.Move;allocation.SetOperands(array,new MemoryOperand(value,addend:16));
        }
        if(shape.StartsWith("multiple-"))guard.Instructions.Insert(0,new(9,OpCode.Move,
            shape=="multiple-array"?array:shape=="multiple-class"?klass:handle,new Immediate(0)));
        if(shape.StartsWith("escaped-"))guard.Instructions.Insert(3,new(10,OpCode.CallVoid,new StringLiteral("observer"),
            new AddressOf(shape=="escaped-array"?array:shape=="escaped-class"?klass:handle)));
        if(shape=="late-class-load"){guard.Instructions.Remove(classLoad);guard.Instructions.Insert(guard.Instructions.IndexOf(call)+1,classLoad);}
        if(shape=="bypass-allocation"){guard.Instructions.Remove(allocation);store.Instructions.Insert(0,allocation);}
        if(shape=="wrong-class-type")klass.Type=types.SystemObjectType;
        if(shape=="wrong-element-type")handle.Type=new RuntimeClassTypeAnalysisContext(types.SystemObjectType,arrayType.DeclaringAssembly);
        var original=graph.Instructions.ToArray();var operands=call.Operands.ToArray();
        if(shape=="normal")
        {
            Assert.That(AllocatedArrayElementClassRecovery.Run(method),Is.Zero,"unreviewed test image must not enter production rewriting");
            Assert.That(call.OpCode,Is.EqualTo(OpCode.Call));
        }
        Assert.That(AllocatedArrayElementClassRecovery.TryRewrite(method,call),Is.EqualTo(expected));
        Assert.That(graph.Instructions,Is.EqualTo(original));
        Assert.That(guard.Successors,Is.EquivalentTo(new[]{store,failure}));
        Assert.That(guard.Instructions.Contains(comparison)&&guard.Instructions.Contains(branch),Is.True);
        Assert.That(store.Instructions.Contains(write)&&failure.Instructions.Contains(throwInstruction),Is.True);
        Assert.That(throwInstruction.Operands[0],Is.EqualTo(thrown));
        if(expected)
        {
            Assert.That(call.OpCode,Is.EqualTo(OpCode.IsInst));
            Assert.That(call.Operands.ToArray(),Is.EqualTo(new IOperand[]{result,element,input}));
            Assert.That(comparison.Operands[1],Is.SameAs(result)); // null still follows original failure path
        }
        else
        {
            Assert.That(call.OpCode,Is.EqualTo(OpCode.Call));Assert.That(call.Operands.ToArray(),Is.EqualTo(operands));
        }
    }
}
