using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class ExceptionWrapperShapeTests
{
    private static bool Shape(byte[] bytes, params ulong[] raises) =>
        NewArmV8InstructionSet.HasExceptionWrapperShape(
            Disassembler.Disassemble(bytes,0x1000,new(true,true,false)).ToList(),new HashSet<ulong>(raises));

    [Test]
    public void ReturningWrapperDoesNotReadTheFollowingFunction()
    {
        // BL +4; RET; STR X1,[X0].
        Assert.That(Shape([1,0,0,0x94,0xC0,3,0x5F,0xD6,1,0,0,0xF9]),Is.True);
    }

    [Test]
    public void ConditionalErrorPathDoesNotMakeTheFunctionAnExceptionWrapper()
    {
        // CBZ X0,+4; BL +4; RET.
        Assert.That(Shape([0x20,0,0,0xB4,1,0,0,0x94,0xC0,3,0x5F,0xD6]),Is.False);
    }

    [Test]
    public void OutputMutationIsNotExceptionTransport()
    {
        // STR X1,[X0]; BL +4; RET.
        Assert.That(Shape([1,0,0,0xF9,1,0,0,0x94,0xC0,3,0x5F,0xD6]),Is.False);
    }

    [Test]
    public void StackSpillCanBelongToAWrapper()
    {
        // STR X1,[SP]; BL +4; RET.
        Assert.That(Shape([0xE1,3,0,0xF9,1,0,0,0x94,0xC0,3,0x5F,0xD6]),Is.True);
    }

    [Test]
    public void UnknownFramePointerIsNotAssumedToBeStack()
    {
        // STR X1,[X29]; RET. X29 may be an application pointer.
        Assert.That(Shape([0xA1,3,0,0xF9,0xC0,3,0x5F,0xD6]),Is.False);
    }

    [Test]
    public void PositivelyResolvedRaiseTerminatesTheBody()
    {
        // BL +4 to the resolved non-returning raise; following bytes are not reached.
        Assert.That(Shape([1,0,0,0x94,1,0,0,0xF9],0x1004),Is.True);
        Assert.That(Shape([1,0,0,0x94,1,0,0,0xF9]),Is.False);
    }

    [Test]
    public void UnterminatedScanAndIndirectCallsRemainUnknown()
    {
        Assert.That(Shape([0x1F,0x20,3,0xD5]),Is.False); // NOP, no terminal
        Assert.That(Shape([0,0,0x3F,0xD6,0xC0,3,0x5F,0xD6]),Is.False); // BLR X0; RET
    }
}
