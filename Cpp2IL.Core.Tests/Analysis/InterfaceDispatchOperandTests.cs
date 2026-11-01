using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceDispatchOperandTests
{
    [TestCase(0, 16)]
    [TestCase(16, 0)]
    [TestCase(0, 0)]
    public void Arm64ZeroRegisterOrMaterializesExactSlot(long left, long right)
    {
        var slot = new LocalVariable("slot", new Register(2, "X2", 1));
        var defs = new Dictionary<LocalVariable, Instruction>
        {
            [slot] = new(0, OpCode.Or, slot, new Immediate(left), new Immediate(right))
        };
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(slot, defs), Is.EqualTo(new Immediate(left | right)));
    }

    [TestCase(1, 16, 0)]
    [TestCase(0, 16, 4)]
    public void ArbitraryOrAndFloatingPayloadsAreNotDispatchMetadata(long left, long right, int floatingWidth)
    {
        var slot = new LocalVariable("slot", new Register(2, "X2", 1));
        var instruction = new Instruction(0, OpCode.Or, slot, new Immediate(left), new Immediate(right))
            { NativeFloatingPointSize = floatingWidth };
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(slot,
            new Dictionary<LocalVariable, Instruction> { [slot] = instruction }), Is.Null);
    }

    [Test]
    public void DirectMetadataAndSlotRemainExactObjects()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemStringType;
        var slot=new Immediate(0);
        var defs=new Dictionary<LocalVariable,Instruction>();
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(type,defs),Is.SameAs(type));
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(slot,defs),Is.EqualTo(slot));
    }

    [Test]
    public void ProvenMoveChainsResolveWithoutInferringLocalTypes()
    {
        var one=new LocalVariable("one",new Register(null,"x1"));
        var two=new LocalVariable("two",new Register(null,"x2"));
        var slot=new Immediate(3);
        var defs=new Dictionary<LocalVariable,Instruction>
        {
            [one]=new(0,OpCode.Move,one,two),
            [two]=new(1,OpCode.Move,two,slot)
        };
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(one,defs),Is.EqualTo(slot));
        defs[two]=new(1,OpCode.Move,two,one);
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(one,defs),Is.Null);
        defs.Clear();
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(one,defs),Is.Null);
    }

    [Test]
    public void MemoryRegistersAndArithmeticNeverBecomeGuessedMetadata()
    {
        var local=new LocalVariable("value",new Register(null,"x1"));
        var defs=new Dictionary<LocalVariable,Instruction>();
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(new MemoryOperand(local),defs),Is.Null);
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(new Register(null,"x1"),defs),Is.Null);
        defs[local]=new(0,OpCode.Add,local,new Immediate(1),new Immediate(2));
        Assert.That(InterfaceDispatchRecovery.ResolveDispatchOperand(local,defs),Is.Null);
    }
}
