using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64FrameAliasRecoveryTests
{
    [TestCase("preserved",true)]
    [TestCase("self-copy",true)]
    [TestCase("nonvolatile-call",true)]
    [TestCase("nested",true)]
    [TestCase("killed",false)]
    [TestCase("shifted",false)]
    [TestCase("volatile-call",false)]
    [TestCase("unanchored",false)]
    [TestCase("unreachable",false)]
    [TestCase("missing-entry-definition",false)]
    public void LoopsKeepOnlyEntryAnchoredInvariantFrameAddresses(string shape,bool expected)
    {
        foreach(var reverse in new[]{false,true})
        {
            var register=shape=="volatile-call"?"X8":"X29";
            var graph=new ISILControlFlowGraph([]);
            var initial=new Block{ID=2,Instructions=shape is "unanchored" or "missing-entry-definition"?[]:[Root(name:register)]};
            var read=Read(1,register);var loop=new Block{ID=3,Instructions=[read]};var back=new Block{ID=4};
            if(shape=="killed")back.Instructions.Add(new(2,OpCode.Move,R(register),new Immediate(0)));
            if(shape=="shifted")back.Instructions.Add(new Instruction(2,OpCode.Add,R(register),R(register),new Immediate(4)){NativeArithmeticSize=8});
            if(shape=="self-copy")back.Instructions.Add(new Instruction(2,OpCode.Move,R(register),R(register)){NativeRegisterCopySize=8});
            if(shape is "nonvolatile-call" or "volatile-call")back.Instructions.Add(new(2,OpCode.CallVoid,new Immediate(0x1000)));
            if(shape=="missing-entry-definition")back.Instructions.Add(Root(2,register));
            graph.EntryBlock.Successors=[initial];initial.Predecessors=[graph.EntryBlock];initial.Successors=[loop];
            loop.Predecessors=[initial,back];loop.Successors=[back,graph.ExitBlock];back.Predecessors=[loop];back.Successors=[loop];
            graph.ExitBlock.Predecessors=[loop];graph.Blocks=[graph.EntryBlock,initial,loop,back,graph.ExitBlock];
            if(shape=="nested")
            {
                var inner=new Block{ID=5};loop.Successors=[inner,graph.ExitBlock];inner.Predecessors=[loop,inner];
                inner.Successors=[inner,back];back.Predecessors=[inner];graph.Blocks.Add(inner);
            }
            if(shape=="unreachable")
            {
                graph.EntryBlock.Successors=[graph.ExitBlock];graph.ExitBlock.Predecessors=[graph.EntryBlock];initial.Predecessors=[];
            }
            if(reverse)graph.Blocks.Reverse();
            Arm64FrameAliasRecovery.Recover(graph,graph.Instructions.ToDictionary(i=>i,_=>-0x80));
            Assert.That(read.Operands[1] is StackOffset,Is.EqualTo(expected),shape+" reversed="+reverse);
            if(expected)Assert.That(read.Operands[1],Is.EqualTo(new StackOffset(0x38)));
        }
    }

    private static Register R(string name) => new(null, name);
    private static Instruction Root(int index = 0, string name = "X29") =>
        new(index, OpCode.Move, R(name), new AddressOf(new StackOffset(0x70))) { NativeRegisterCopySize = 8 };
    private static Instruction Read(int index, string name = "X29", long displacement = -0x38) =>
        new(index, OpCode.Move, R("X20"), new MemoryOperand(R(name), addend: displacement));
    private static (ISILControlFlowGraph Graph, Dictionary<Instruction, int> Sizes) Graph(params Instruction[] instructions)
    {
        var graph = new ISILControlFlowGraph(instructions.ToList());
        return (graph, instructions.ToDictionary(i => i, _ => -0x80));
    }

    [Test]
    public void FrameMemoryAndByrefAddressBecomeSameStackSlot()
    {
        var root = Root(); var load = Read(1);
        var address = new Instruction(2, OpCode.Subtract, R("X2"), R("X29"), new Immediate(0x38)) { NativeArithmeticSize = 8 };
        var (graph, sizes) = Graph(root, load, address);
        Assert.That(Arm64FrameAliasRecovery.Recover(graph, sizes), Is.EqualTo(2));
        Assert.That(load.Operands[1], Is.EqualTo(new StackOffset(0x38)));
        Assert.That(address.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(address.Operands[1], Is.EqualTo(new AddressOf(new StackOffset(0x38))));
    }

    [TestCase(0, false)]
    [TestCase(4, false)]
    [TestCase(8, true)]
    public void OnlyProvenFullWidthCopiesPropagate(int width, bool recovered)
    {
        var copy = new Instruction(1, OpCode.Move, R("X23"), R("X29")) { NativeRegisterCopySize = width };
        var read = Read(2, "X23"); var (graph, sizes) = Graph(Root(), copy, read);
        Arm64FrameAliasRecovery.Recover(graph, sizes);
        Assert.That(read.Operands[1] is StackOffset, Is.EqualTo(recovered));
    }

    [TestCase("X8", false)]
    [TestCase("X19", true)]
    [TestCase("X29", true)]
    [TestCase("X30", false)]
    public void CallClobbersOnlyVolatileAliases(string name, bool recovered)
    {
        var read = Read(2, name);
        var (graph, sizes) = Graph(Root(name:name), new Instruction(1, OpCode.CallVoid, new Immediate(0x1000)), read);
        Arm64FrameAliasRecovery.Recover(graph, sizes);
        Assert.That(read.Operands[1] is StackOffset, Is.EqualTo(recovered));
    }

    [Test]
    public void EpilogueRestoreDoesNotInvalidateEarlierFrameReads()
    {
        var before = Read(1); var after = Read(3);
        var restore = new Instruction(2, OpCode.Move, R("X29"), new StackOffset(0x70));
        var (graph, sizes) = Graph(Root(), before, restore, after);
        Arm64FrameAliasRecovery.Recover(graph, sizes);
        Assert.That(before.Operands[1], Is.TypeOf<StackOffset>());
        Assert.That(after.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void StackAdjustmentUsesPerInstructionCoordinate()
    {
        var root = Root(); var read = Read(1); var (graph, sizes) = Graph(root, read);
        sizes[read] = -0x90;
        Arm64FrameAliasRecovery.Recover(graph, sizes);
        Assert.That(read.Operands[1], Is.EqualTo(new StackOffset(0x48)));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void JoinsRequireSameAddressOnEveryPredecessor(bool same)
    {
        var graph = new ISILControlFlowGraph([]);
        var left = new Block { Instructions = [Root()] };
        var rightRoot = Root(1); if (!same) rightRoot.SetOperand(1, new AddressOf(new StackOffset(0x60)));
        var right = new Block { Instructions = [rightRoot] };
        var read = Read(2); var join = new Block { Instructions = [read] };
        graph.EntryBlock.Successors = [left, right];
        left.Predecessors = [graph.EntryBlock]; right.Predecessors = [graph.EntryBlock];
        left.Successors = [join]; right.Successors = [join]; join.Predecessors = [left, right];
        join.Successors = [graph.ExitBlock]; graph.ExitBlock.Predecessors = [join];
        graph.Blocks = [graph.EntryBlock, left, right, join, graph.ExitBlock];
        var sizes = graph.Instructions.ToDictionary(i => i, _ => -0x80);
        Arm64FrameAliasRecovery.Recover(graph, sizes);
        Assert.That(read.Operands[1] is StackOffset, Is.EqualTo(same));
    }

    [Test]
    public void UnknownPointerDynamicIndexAndOverflowRemainUntouched()
    {
        var unknown = Read(0, "X28"); var huge = Read(2, displacement:long.MaxValue);
        var indexed = new Instruction(3, OpCode.Move, R("X1"), new MemoryOperand(R("X29"), R("X3"), 4, 8));
        var (graph, sizes) = Graph(unknown, Root(1), huge, indexed);
        Assert.That(Arm64FrameAliasRecovery.Recover(graph, sizes), Is.Zero);
    }

    [Test]
    public void LoopBackedgeWithReassignmentCannotLeakAnEarlyAlias()
    {
        var graph = new ISILControlFlowGraph([]);
        var initial = new Block { Instructions = [Root()] };
        var read = Read(1); var loop = new Block { Instructions = [read] };
        var kill = new Block { Instructions = [new Instruction(2, OpCode.Move, R("X29"), new Immediate(0))] };
        graph.EntryBlock.Successors = [initial]; initial.Predecessors = [graph.EntryBlock]; initial.Successors = [loop];
        loop.Predecessors = [initial, kill]; loop.Successors = [kill, graph.ExitBlock];
        kill.Predecessors = [loop]; kill.Successors = [loop]; graph.ExitBlock.Predecessors = [loop];
        graph.Blocks = [graph.EntryBlock, initial, loop, kill, graph.ExitBlock];
        Arm64FrameAliasRecovery.Recover(graph, graph.Instructions.ToDictionary(i => i, _ => -0x80));
        Assert.That(read.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [TestCase(0x91, 8)]
    [TestCase(0x11, 0)]
    public void ActualArm64StackAddressInstructionRetainsWidth(byte high, int expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "FrameWidth",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        // add x29/w29,sp/wsp,#0x70; the W variant truncates a pointer.
        var native = Disassembler.Disassemble(new byte[]{0xfd,0xc3,0x01,high}, 0x1000, new(true,true,false)).Single();
        var emitted = new List<Instruction>(); var addresses = new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[]{native, emitted, addresses, method});
        Assert.That(emitted.Single().NativeRegisterCopySize, Is.EqualTo(expected));
    }

    [Test]
    public void RealStackAnalyzerRetainsInstructionLookupAfterOperandMutation()
    {
        var app = TestGameLoader.LoadSimple2019Game(); app.InstructionSet = new NewArmV8InstructionSet();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "FrameLookup",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var read = Read(2);
        method.ParameterOperands = [];
        method.ControlFlowGraph = new([new Instruction(0, OpCode.ShiftStack, new Immediate(-0x80)),
            Root(1), read, new Instruction(3, OpCode.ShiftStack, new Immediate(0x80)), new Instruction(4, OpCode.Return)]);
        StackAnalyzer.Analyze(method);
        Assert.That(read.Operands[1], Is.EqualTo(R("stack_-48")));
    }
}
