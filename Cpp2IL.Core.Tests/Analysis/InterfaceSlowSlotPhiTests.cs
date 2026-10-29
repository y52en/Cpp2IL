using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceSlowSlotPhiTests
{
    [TestCase("valid",true)]
    [TestCase("copy",true)]
    [TestCase("foreign-info",false)]
    [TestCase("partial-info",false)]
    [TestCase("wrong-info-offset",false)]
    [TestCase("same-number-other-slot",false)]
    [TestCase("unmatched-slot",false)]
    [TestCase("raw-constant",false)]
    [TestCase("unbound-slot",false)]
    [TestCase("effectful-other-leaf",false)]
    [TestCase("cycle",false)]
    [TestCase("only-slot",false)]
    [TestCase("only-info",false)]
    public void OnlyCompleteMatchedMetadataAndActualSlowSlotQualify(string shape,bool expected)
    {
        LocalVariable Local(string name)=>new(name,new(null,name));
        var lookup=Local("lookup");var foreign=Local("foreign");var info=Local("info");
        var slot=Local("slot");var other=Local("same-value");var merged=Local("merged");var copied=Local("copied");
        var matched=new Instruction(-1,OpCode.Phi,lookup,new Immediate(0),new Immediate(1));
        var read=new Instruction(1,OpCode.Move,info,new MemoryOperand(shape=="foreign-info"?foreign:lookup,
            addend:shape=="wrong-info-offset"?0:8)){NativeReadSize=shape=="partial-info"?4:8};
        var slotDef=new Instruction(2,OpCode.Or,slot,new Immediate(0),new Immediate(1));
        IOperand alternative=shape switch{"raw-constant"=>new Immediate(1),"same-number-other-slot"=>other,_=>slot};
        var phi=new Instruction(-1,OpCode.Phi,merged,info,alternative);
        var defs=new Dictionary<LocalVariable,Instruction>{{lookup,matched},{info,read},{slot,slotDef},
            {other,new(3,OpCode.Or,other,new Immediate(0),new Immediate(1))},{merged,phi}};
        if(shape=="unbound-slot")defs.Remove(slot);
        if(shape=="effectful-other-leaf")phi.SetOperand(2,new MemoryOperand(slot));
        if(shape=="cycle")phi.SetOperand(2,merged);
        if(shape=="only-slot")phi.SetOperand(1,slot);
        if(shape=="only-info")phi.SetOperand(2,info);
        IOperand input=merged;
        if(shape=="copy"){defs[copied]=new(4,OpCode.Move,copied,merged);input=copied;}
        Assert.That(InterfaceDispatchRecovery.IsMatchedSlowSlotPhi(input,defs,[matched],
            shape=="unmatched-slot"?[]:[slot]),Is.EqualTo(expected));
        // Existing metadata-only policy remains unchanged for nonzero slots.
        Assert.That(InterfaceDispatchRecovery.IsMatchedLookupMetadataPhi(input,defs,[],[matched]),Is.False);
    }
}
