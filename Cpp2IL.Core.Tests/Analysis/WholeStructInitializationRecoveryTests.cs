using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class WholeStructInitializationRecoveryTests
{
    [TestCase("complete")]
    [TestCase("reordered")]
    [TestCase("partial")]
    [TestCase("overlap")]
    [TestCase("nonzero")]
    [TestCase("unknownwidth")]
    [TestCase("interveningcall")]
    public void OnlyExactFullWidthZeroCoverageBecomesDefault(string shape)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Data",types.SystemValueTypeType,TypeAttributes.Public);
        var root=new Register(null,"stack_-80");var block=new Block();
        var names=shape=="reordered"?new[]{"stack_-78","stack_-80","stack_-68","stack_-70"}:new[]{"stack_-80","stack_-78","stack_-70","stack_-68"};
        for(var i=0;i<4;i++) block.Instructions.Add(new Instruction(i,OpCode.Move,new Register(null,names[i]),new Immediate(shape=="nonzero"&&i==2?1:0)){NativeWriteSize=shape=="partial"?4:shape=="unknownwidth"?0:8});
        if(shape=="overlap") block.Instructions[2].SetOperand(0,root);
        if(shape=="interveningcall") block.Instructions.Insert(2,new(5,OpCode.CallVoid,new Immediate(123)));
        var expected=shape is "complete" or "reordered";
        Assert.That(WholeStructInitializationRecovery.RecoverGroup(block,0,root,type,32),Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(block.Instructions[0].Operands[1],Is.TypeOf<DefaultStructValue>());
            Assert.That(block.Instructions.Skip(1).All(i=>i.OpCode==OpCode.Nop),Is.True);
            Assert.That(WholeStructInitializationRecovery.RecoverGroup(block,0,root,type,32),Is.False);
        }
        else Assert.That(block.Instructions[0].Operands[1],Is.TypeOf<Immediate>());
    }

    [TestCase(Arm64Mnemonic.STR,Arm64Register.W31,4)]
    [TestCase(Arm64Mnemonic.STR,Arm64Register.X31,8)]
    [TestCase(Arm64Mnemonic.STR,Arm64Register.V0,16)]
    [TestCase(Arm64Mnemonic.STRB,Arm64Register.W0,1)]
    [TestCase(Arm64Mnemonic.STURH,Arm64Register.W0,2)]
    public void NativeStoreWidthIsNotLost(Arm64Mnemonic mnemonic,Arm64Register register,int expected)
        => Assert.That(NewArmV8InstructionSet.StoreWidth(mnemonic,register),Is.EqualTo(expected));
}
