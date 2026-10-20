using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class EmptyRuntimeGuardRecoveryTests
{
    [TestCase("forward",2)]
    [TestCase("reverse",2)]
    [TestCase("live-copy",1)]
    [TestCase("effect",0)]
    [TestCase("unknown-mask",0)]
    public void LaterDiamondCleanupEnablesEarlierGuardWithoutDiscardingLiveCopies(string shape,int expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var klass=new LocalVariable("klass",new Register(null,"klass"),new RuntimeClassTypeAnalysisContext(t.SystemObjectType,t.SystemObjectType.DeclaringAssembly));
        var alias=new LocalVariable("alias",new Register(null,"alias"),klass.Type);
        var cfg=new ISILControlFlowGraph([]);
        var first=new Block{ID=2};var firstEmpty=new Block{ID=3};var second=new Block{ID=4};
        var secondEmpty=new Block{ID=5};var merge=new Block{ID=6};
        cfg.Blocks.AddRange(shape=="reverse" ? [second,secondEmpty,merge,first,firstEmpty] : [first,firstEmpty,second,secondEmpty,merge]);
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(cfg.EntryBlock,first);Edge(first,firstEmpty);Edge(first,second);Edge(firstEmpty,second);
        Edge(second,secondEmpty);Edge(second,merge);Edge(secondEmpty,merge);Edge(merge,cfg.ExitBlock);
        void Guard(Block b,LocalVariable handle,Block target,int maskValue)
        {
            var mask=new LocalVariable("m"+b.ID,new Register(null,"m"+b.ID),t.SystemInt32Type);
            var predicate=new LocalVariable("p"+b.ID,new Register(null,"p"+b.ID),t.SystemBooleanType);
            b.Instructions=[new(b.ID*10,OpCode.And,mask,new MemoryOperand(handle,addend:0x127),new Immediate(maskValue)),
                new(b.ID*10+1,OpCode.CheckEqual,predicate,mask,new Immediate(0)),new(b.ID*10+2,OpCode.ConditionalJump,target,predicate)];
            b.CalculateBlockType();
        }
        Guard(first,klass,second,2);first.Instructions.Insert(0,new(1,OpCode.Move,alias,klass));
        firstEmpty.Instructions=[new(30,OpCode.Move,alias,klass),new(31,OpCode.Jump,second)];
        Guard(second,alias,merge,shape=="unknown-mask" ? 4 : 2);
        secondEmpty.Instructions=[new(50,OpCode.Nop),new(51,OpCode.Jump,merge)];
        if(shape=="effect")secondEmpty.Instructions.Insert(0,new(52,OpCode.CallVoid,new StringLiteral("effect")));
        var business=new Instruction(60,OpCode.CallVoid,new StringLiteral("business"));
        if(shape=="live-copy")business.SetOperands(new StringLiteral("business"),alias);
        merge.Instructions=[business,new(61,OpCode.Return)];
        Assert.That(EmptyRuntimeGuardRecovery.RecoverToFixedPoint(cfg),Is.EqualTo(expected));
        Assert.That(merge.Instructions.Contains(business),Is.True);
        Assert.That(EmptyRuntimeGuardRecovery.RecoverToFixedPoint(cfg),Is.Zero);
        if(shape=="live-copy")Assert.That(firstEmpty.Instructions[0].OpCode,Is.EqualTo(OpCode.Move));
    }

    [TestCase("cctor", true)]
    [TestCase("initialized", true)]
    [TestCase("callback", false)]
    [TestCase("store", false)]
    [TestCase("local-copy", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("wrong-mask", false)]
    [TestCase("object-not-class", false)]
    [TestCase("shared-region", false)]
    [TestCase("loop", false)]
    [TestCase("phi", false)]
    [TestCase("other-predicate", false)]
    [TestCase("snapshot", true)]
    [TestCase("snapshot-wide", false)]
    [TestCase("snapshot-redefined", false)]
    public void CollapseOnlyAnEmptyKnownClassFlagDiamond(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var types = app.SystemTypes;
        var klass = new LocalVariable("klass", new Register(null, "klass"), shape == "object-not-class"
            ? types.SystemObjectType : new RuntimeClassTypeAnalysisContext(types.SystemObjectType, types.SystemObjectType.DeclaringAssembly));
        var mask = new LocalVariable("mask", new Register(null, "mask"), types.SystemInt32Type);
        var flag = new LocalVariable("flag", new Register(null, "flag"), types.SystemBooleanType);
        var other = new LocalVariable("other", new Register(null, "other"), types.SystemBooleanType);
        var cfg = new ISILControlFlowGraph([]);
        var guard = new Block { ID = 2 }; var empty = new Block { ID = 3 }; var merge = new Block { ID = 4 };
        cfg.Blocks.AddRange([guard, empty, merge]);
        void Edge(Block a, Block b) { a.Successors.Add(b); b.Predecessors.Add(a); }
        Edge(cfg.EntryBlock, guard); Edge(guard, empty); Edge(guard, merge); Edge(empty, merge); Edge(merge, cfg.ExitBlock);
        var print = new Instruction(0, OpCode.CallVoid, new StringLiteral("business-print"));
        guard.Instructions = [print,
            new(1, OpCode.And, mask, new MemoryOperand(klass, addend: shape == "wrong-offset" ? 0x128 : shape == "initialized" ? 0x126 : 0x127), new Immediate(shape == "wrong-mask" ? 4 : shape == "initialized" ? 1 : 2)),
            new(2, OpCode.CheckEqual, flag, mask, new Immediate(0)),
            new(3, OpCode.ConditionalJump, merge, shape == "other-predicate" ? other : flag)];
        if(shape.StartsWith("snapshot",System.StringComparison.Ordinal))
        {
            var snapshot=new LocalVariable("snapshot",new Register(null,"snapshot"),types.SystemInt32Type);
            var memory=guard.Instructions[1].Operands[1];
            guard.Instructions[1].SetOperand(1,snapshot);
            guard.Instructions.Insert(1,new(10,OpCode.Move,snapshot,memory){NativeReadSize=shape=="snapshot-wide"?4:1});
            if(shape=="snapshot-redefined")guard.Instructions.Insert(2,new(11,OpCode.Move,snapshot,new Immediate(0)));
        }
        empty.Instructions = [new(4, OpCode.Nop), new(5, OpCode.Jump, merge)];
        var business = new Instruction(6, OpCode.CallVoid, new StringLiteral("business-call"));
        merge.Instructions = [business, new(7, OpCode.Return)];
        if (shape == "callback") empty.Instructions.Insert(0, new(8, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "store") empty.Instructions.Insert(0, new(8, OpCode.Move, new MemoryOperand(klass), new Immediate(0)));
        if (shape == "local-copy") empty.Instructions.Insert(0, new(8, OpCode.Move, other, flag));
        if (shape == "shared-region") Edge(cfg.EntryBlock, empty);
        if (shape == "loop") { cfg.RemoveEdge(empty, merge); Edge(empty, empty); empty.Instructions[^1].SetOperand(0, empty); }
        if (shape == "phi") merge.Instructions.Insert(0, new(8, OpCode.Phi, other, flag, new Immediate(0)));
        foreach (var block in cfg.Blocks) block.CalculateBlockType();
        Assert.That(EmptyRuntimeGuardRecovery.TryRecover(cfg, guard), Is.EqualTo(expected));
        Assert.That(guard.Instructions.Contains(print), Is.True);
        Assert.That(merge.Instructions.Contains(business), Is.True);
        Assert.That(cfg.Blocks.Contains(empty), Is.EqualTo(!expected));
    }
}
