using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlineClassTestRecoveryTests
{
    [TestCase("valid",true)]
    [TestCase("unequal-to-failure",true)]
    [TestCase("ge-to-ancestor",true)]
    [TestCase("not-depth-to-ancestor",true)]
    [TestCase("not-equal-to-failure",true)]
    [TestCase("nullable-success-join",true)]
    [TestCase("source-redefined",false)]
    [TestCase("source-unanchored",false)]
    [TestCase("source-in-guard",true)]
    [TestCase("source-two-definitions",false)]
    [TestCase("source-in-removed-kernel",false)]
    [TestCase("width",false)]
    [TestCase("zero-width",false)]
    [TestCase("extra-read",false)]
    [TestCase("callback",false)]
    [TestCase("ancestor-callback",false)]
    [TestCase("escaping-kernel-local",false)]
    [TestCase("wrong-null-object",false)]
    [TestCase("wrong-ancestor-offset",false)]
    [TestCase("wrong-slot-width",false)]
    [TestCase("unknown-object-type",false)]
    [TestCase("value-object-type",false)]
    [TestCase("byref-object-type",false)]
    [TestCase("redefined-class",false)]
    [TestCase("managed-read",false)]
    [TestCase("array-length-read",false)]
    public void OnlyCompleteClassTestKernelIsReplacedAndBothApplicationOutcomesSurvive(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new(null,name),type);
        var obj=Local("obj",t.SystemObjectType);var other=Local("other",t.SystemObjectType);
        if(shape=="unknown-object-type")obj.Type=null;
        if(shape=="value-object-type")obj.Type=t.SystemInt64Type;
        if(shape=="byref-object-type")obj.Type=new ByRefTypeAnalysisContext(t.SystemObjectType);
        var klass=Local("klass",new RuntimeClassTypeAnalysisContext(t.SystemObjectType,t.SystemObjectType.DeclaringAssembly));
        var target=Local("target",new RuntimeClassTypeAnalysisContext(t.SystemStringType,t.SystemStringType.DeclaringAssembly));
        var sd=Local("sourceDepth");var td=Local("targetDepth");var table=Local("table");
        var shift=Local("shift");var address=Local("address");var slot=Local("slot");
        var nullFlag=Local("nullFlag",t.SystemBooleanType);var shallow=Local("shallow",t.SystemBooleanType);
        var equal=Local("equal",t.SystemBooleanType);
        var cfg=new ISILControlFlowGraph([]);
        var guard=new Block{ID=20};var depth=new Block{ID=21};var ancestor=new Block{ID=22};
        var fail=new Block{ID=23};var success=new Block{ID=24};var nullExit=new Block{ID=25};
        cfg.Blocks=[cfg.EntryBlock,cfg.ExitBlock,guard,depth,ancestor,fail,success,nullExit];
        // The empty-graph constructor creates a placeholder body block. Remove
        // both ends of its edges when replacing the graph with this fixture.
        foreach(var block in cfg.Blocks)
        {
            block.Predecessors.Clear();block.Successors.Clear();
        }
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(cfg.EntryBlock,guard);Edge(guard,depth);Edge(guard,nullExit);
        Edge(depth,ancestor);Edge(depth,fail);Edge(ancestor,success);Edge(ancestor,fail);
        Edge(fail,cfg.ExitBlock);Edge(success,cfg.ExitBlock);Edge(nullExit,cfg.ExitBlock);
        guard.Instructions=[new(0,OpCode.CheckEqual,nullFlag,shape=="wrong-null-object"?other:obj,new Immediate(0)),
            new(1,OpCode.ConditionalJump,nullExit,nullFlag)];
        var sourceDepth=new Instruction(4,OpCode.Move,sd,new MemoryOperand(klass,addend:0x120))
            {NativeReadSize=shape=="width"?8:shape=="zero-width"?0:1};
        depth.Instructions=[new(2,OpCode.Move,klass,new MemoryOperand(obj)){NativeReadSize=8},
            new(3,OpCode.Move,target,t.SystemStringType),sourceDepth,
            new(5,OpCode.Move,td,new MemoryOperand(target,addend:0x120)){NativeReadSize=1},
            new(6,OpCode.CheckLess,shallow,sd,td),new(7,OpCode.ConditionalJump,fail,shallow)];
        ancestor.Instructions=[new(8,OpCode.Move,table,new MemoryOperand(klass,addend:0xC8)){NativeReadSize=8},
            new(9,OpCode.ShiftLeft,shift,td,new Immediate(3)),new(10,OpCode.Add,address,table,shift),
            new(11,OpCode.Move,slot,new MemoryOperand(address,addend:shape=="wrong-ancestor-offset"?-16:-8))
                {NativeReadSize=shape=="wrong-slot-width"?4:8},
            new(12,OpCode.CheckEqual,equal,slot,t.SystemStringType),new(13,OpCode.ConditionalJump,success,equal)];
        if(shape=="unequal-to-failure")
        {
            ancestor.Instructions[^2].OpCode=OpCode.CheckNotEqual;
            ancestor.Instructions[^1].SetOperand(0,fail);
        }
        if(shape=="ge-to-ancestor")
        {
            depth.Instructions[^2].OpCode=OpCode.CheckGreaterOrEqual;
            depth.Instructions[^1].SetOperand(0,ancestor);
        }
        if(shape=="not-depth-to-ancestor")
        {
            var inverse=Local("depthInverse",t.SystemBooleanType);
            depth.Instructions.Insert(depth.Instructions.Count-1,new(19,OpCode.Not,inverse,shallow));
            depth.Instructions[^1].SetOperands(ancestor,inverse);
        }
        if(shape=="not-equal-to-failure")
        {
            var inverse=Local("equalInverse",t.SystemBooleanType);
            ancestor.Instructions.Insert(ancestor.Instructions.Count-1,new(19,OpCode.Not,inverse,equal));
            ancestor.Instructions[^1].SetOperands(fail,inverse);
        }
        var fallback=new Instruction(14,OpCode.CallVoid,new StringLiteral("observable-fallback"),obj);
        var application=new Instruction(16,OpCode.CallVoid,new StringLiteral("observable-success"),obj);
        fail.Instructions=[fallback,new(15,OpCode.Return)];success.Instructions=[application,new(17,OpCode.Return)];
        nullExit.Instructions=[new(18,OpCode.Return)];
        if(shape=="extra-read")depth.Instructions.Insert(1,new(19,OpCode.Move,Local("extra"),new MemoryOperand(obj,addend:16)){NativeReadSize=8});
        if(shape=="callback")depth.Instructions.Insert(1,new(19,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="ancestor-callback")ancestor.Instructions.Insert(1,new(19,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="escaping-kernel-local")fallback.SetOperands(new StringLiteral("observable-fallback"),table);
        if(shape=="redefined-class")ancestor.Instructions.Insert(0,new(19,OpCode.Move,klass,new MemoryOperand(other)){NativeReadSize=8});
        if(shape=="array-length-read")depth.Instructions.Insert(0,new(19,OpCode.Move,Local("extra"),new ArrayLength(other)));
        if(shape=="managed-read")
        {
            var holder=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Holder",t.SystemObjectType,TypeAttributes.Public);
            var field=holder.InjectFieldContext("Value",t.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
            depth.Instructions.Insert(0,new(19,OpCode.Move,Local("extra"),new FieldReference(field,other,16)));
        }
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=cfg};
        method.ParameterLocals=[obj,other];
        if(shape=="source-redefined")success.Instructions.Insert(0,new(19,OpCode.Move,obj,other));
        if(shape=="source-unanchored")method.ParameterLocals=[other];
        if(shape is "source-in-guard" or "source-two-definitions")
        {
            method.ParameterLocals=[other];guard.Instructions.Insert(0,new(19,OpCode.Move,obj,other));
            if(shape=="source-two-definitions")success.Instructions.Insert(0,new(20,OpCode.Move,obj,other));
        }
        if(shape=="nullable-success-join")
        {
            cfg.RemoveEdge(guard,nullExit);Edge(guard,success);guard.Instructions[^1].SetOperand(0,success);
        }
        if(shape=="source-in-removed-kernel")
        {
            method.ParameterLocals=[other];depth.Instructions.Insert(0,new(19,OpCode.Move,obj,other));
            guard.Instructions[0].SetOperand(1,other);application.SetOperand(1,other);fallback.SetOperand(1,other);
        }
        var original=cfg.Instructions.ToArray();
        Assert.That(InlineClassTestRecovery.Recover(method),Is.EqualTo(expected?1:0));
        Assert.That(cfg.Instructions.Contains(fallback),Is.True);
        Assert.That(cfg.Instructions.Contains(application),Is.True);
        Assert.That(cfg.Blocks.Contains(fail) && cfg.Blocks.Contains(success),Is.True);
        Assert.That(cfg.Instructions.Count(i=>i.OpCode==OpCode.IsInst),Is.EqualTo(expected?1:0));
        Assert.That(cfg.Instructions.Any(i=>i.OpCode==OpCode.CastClass),Is.False);
        if(expected)
        {
            Assert.That(cfg.Blocks.Contains(ancestor),Is.False);
            Assert.That(application.Operands[1],Is.Not.SameAs(obj));
            Assert.That(fallback.Operands[1],Is.SameAs(obj));
            if(shape=="nullable-success-join")
                Assert.That(guard.Instructions.Any(i=>i.OpCode==OpCode.IsInst),Is.True,
                    "null-bypass success must not read an uninitialized check result");
        }
        else Assert.That(cfg.Instructions,Is.EqualTo(original));
    }
}
