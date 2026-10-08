using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceVTableChainTests
{
    [TestCase(true, 296, 4, 0, true)]
    [TestCase(false, 296, 4, 0, true)]
    [TestCase(true, 288, 4, 0, false)]
    [TestCase(false, 288, 4, 0, false)]
    [TestCase(true, 296, 3, 0, false)]
    [TestCase(false, 296, 3, 0, false)]
    [TestCase(true, 296, 4, 1, false)]
    [TestCase(false, 296, 4, 1, false)]
    public void ExactNativeAssociationsRequireScaleOffsetAndSlot(bool outerOffset, long offset, int shift, int slot, bool expected)
    {
        LocalVariable V(string name) => new(name, new Register(null,name));
        var obj=V("obj"); var klass=V("klass"); var entry=V("entry");
        var index=V("index"); var scaled=V("scaled"); var sum=V("sum"); var result=V("result");
        var defs = new Dictionary<LocalVariable,Instruction>
        {
            [klass]=new(0,OpCode.Move,klass,new MemoryOperand(obj)),
            [index]=new(1,OpCode.Move,index,new MemoryOperand(entry)),
            [scaled]=new(2,OpCode.ShiftLeft,scaled,index,new Immediate(shift)),
            [sum]=outerOffset ? new(3,OpCode.Add,sum,klass,scaled) : new(3,OpCode.Add,sum,scaled,new Immediate(offset)),
        };
        var top=outerOffset ? new Instruction(4,OpCode.Add,result,sum,new Immediate(offset)) : new Instruction(4,OpCode.Add,result,klass,sum);
        var match=typeof(InterfaceDispatchRecovery).GetMethod("MatchVTableEntryChain",BindingFlags.NonPublic|BindingFlags.Static)!
            .Invoke(null,new object[]{defs,top,slot,296L});
        Assert.That(match,expected ? Is.SameAs(klass) : Is.Null);
    }
}
