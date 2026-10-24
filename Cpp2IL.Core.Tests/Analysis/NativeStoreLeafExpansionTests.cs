using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeStoreLeafExpansionTests
{
    [TestCase("0004002dc0035fd6",2)]
    [TestCase("0004002d020800bdc0035fd6",3)]
    [TestCase("0004002d1f0800b9c0035fd6",3)]
    [TestCase("0004002d1f0800b9",0)]
    [TestCase("0004002d1f0400b9c0035fd6",0)]
    [TestCase("0004002d1f0400f9c0035fd6",0)]
    [TestCase("0004002d020800b9c0035fd6",0)]
    [TestCase("0004002d1f0800b9c0035fd7",0)]
    [TestCase("0004002d020c012dc0035fd6",4)]
    [TestCase("0004002d020c012dc0035fd6ffffffff",4)]
    [TestCase("0004002d020c012d",0)]
    [TestCase("0004002d020c012dc0035fd7",0)]
    [TestCase("0004002d020c412dc0035fd6",0)]
    [TestCase("0004002d220c012dc0035fd6",0)]
    [TestCase("0004002d020c022dc0035fd6",0)]
    [TestCase("0004002d020c812dc0035fd6",0)]
    [TestCase("0004002dc0035fd6ffffffff",2)]
    [TestCase("0004002d020800bd",0)]
    [TestCase("0004002d",0)]
    [TestCase("0004002dc0035fd7",0)]
    [TestCase("2004002dc0035fd6",0)]
    [TestCase("0004402dc0035fd6",0)]
    [TestCase("0004002d020800bdc0035fd7",0)]
    [TestCase("00000014c0035fd6",0)]
    public void OnlyCompletePositionIndependentNativeStoreRecipesAreRecognized(string code,int lanes)
        => Assert.That(NativeStoreLeafExpansion.LaneCount(System.Convert.FromHexString(code)),Is.EqualTo(lanes));

    [TestCase(false)]
    [TestCase(true)]
    public void ZeroThirdLaneNeverReadsStaleV2(bool isVoid)
    {
        var recipe=NativeStoreLeafExpansion.MatchRecipe(System.Convert.FromHexString("0004002d1f0800b9c0035fd6"));
        Assert.That(recipe,Is.EqualTo(new NativeStoreLeafExpansion.StoreRecipe(2,1)));
        Assert.That(recipe,Is.Not.EqualTo(NativeStoreLeafExpansion.MatchRecipe(System.Convert.FromHexString("0004002d020800bdc0035fd6"))));
        var operands=new System.Collections.Generic.List<IOperand>{new Immediate(0x1234)};
        if(!isVoid)operands.Add(new Register(null,"X0"));
        operands.AddRange(Enumerable.Range(0,16).Select(n=>(IOperand)new Register(null,n<8?"X"+n:"V"+(n-8))));
        var call=new Instruction(7,isVoid?OpCode.CallVoid:OpCode.Call,operands);
        var block=new Block{ID=2,Instructions=[call]};var serial=100;
        Assert.That(NativeStoreLeafExpansion.Rewrite(block,0,recipe,ref serial),Is.True);
        Assert.That(serial,Is.EqualTo(103));Assert.That(block.Instructions[^1],Is.SameAs(call));
        for(var n=0;n<3;n++)
        {
            var store=block.Instructions[n];Assert.That(store.NativeWriteSize,Is.EqualTo(4));
            Assert.That(((MemoryOperand)store.Operands[0]).Addend,Is.EqualTo(n*4));
            if(n<2)Assert.That(store.Operands[1],Is.EqualTo(new Register(null,"V"+n)));
            else Assert.That(((Immediate)store.Operands[1]).Value,Is.Zero);
        }
    }

    [TestCase(2,2)]
    [TestCase(3,1)]
    [TestCase(4,1)]
    [TestCase(2,-1)]
    public void UnprovenMixedRecipesCannotMutateTheGraph(int floating,int zeros)
    {
        var call=new Instruction(7,OpCode.CallVoid,new Immediate(0x1234));
        var block=new Block{ID=2,Instructions=[call]};var serial=100;
        Assert.That(NativeStoreLeafExpansion.Rewrite(block,0,new NativeStoreLeafExpansion.StoreRecipe(floating,zeros),ref serial),Is.False);
        Assert.That(block.Instructions,Is.EqualTo(new[]{call}));Assert.That(call.OpCode,Is.EqualTo(OpCode.CallVoid));
        Assert.That(serial,Is.EqualTo(100));
    }

    [TestCase("pair",true)]
    [TestCase("triple",true)]
    [TestCase("quad",true)]
    [TestCase("quad-void",true)]
    [TestCase("void",true)]
    [TestCase("unsupported-lanes",false)]
    [TestCase("implicit-clobber",false)]
    [TestCase("virtual",false)]
    [TestCase("target",false)]
    [TestCase("arity",false)]
    [TestCase("gpr-order",false)]
    [TestCase("fp-order",false)]
    [TestCase("ssa-register",false)]
    [TestCase("local",false)]
    [TestCase("return-register",false)]
    [TestCase("empty-call",false)]
    [TestCase("target-disagreement",false)]
    public void ExactRawAbiPreservesInstructionIdentityAndDoesNotInventConstructor(string shape,bool expected)
    {
        var args=Enumerable.Range(0,16).Select(n=>(IOperand)new Register(null,n<8?"X"+n:"V"+(n-8))).ToList();
        var operands=new System.Collections.Generic.List<IOperand>{new Immediate(0x1234)};
        var isVoid=shape is "void" or "quad-void";
        if(!isVoid)operands.Add(new Register(null,"X0"));
        operands.AddRange(args);var first=isVoid?1:2;
        if(shape=="target")operands[0]=new StringLiteral("unknown");
        if(shape=="arity")operands.RemoveAt(operands.Count-1);
        if(shape=="gpr-order")operands[first+1]=new Register(null,"X2");
        if(shape=="fp-order")operands[first+8]=new Register(null,"V1");
        if(shape=="ssa-register")operands[first+8]=new Register(null,"V0",1);
        if(shape=="local")operands[first]=new LocalVariable("pointer",new Register(null,"X0"));
        if(shape=="return-register")operands[1]=new Register(null,"X1");
        if(shape=="empty-call")operands.Clear();
        var call=new Instruction(7,isVoid?OpCode.CallVoid:OpCode.Call,operands)
            {NativeVirtualDispatch=shape=="virtual"};
        if(shape=="implicit-clobber")call.ImplicitDefinition=new Register(null,"X0");
        if(shape=="target-disagreement")call.NativeDirectCallTarget=0x9999;
        var block=new Block{ID=2,Instructions=[call]};var before=call.Operands.ToArray();var serial=100;
        var lanes=shape=="triple"?3:shape is "quad" or "quad-void"?4:shape=="unsupported-lanes"?5:2;
        Assert.That(NativeStoreLeafExpansion.Rewrite(block,0,lanes,ref serial),Is.EqualTo(expected));
        if(!expected)
        {Assert.That(block.Instructions,Is.EqualTo(new[]{call}));Assert.That(call.Operands,Is.EqualTo(before));Assert.That(serial,Is.EqualTo(100));return;}
        Assert.That(block.Instructions[^1],Is.SameAs(call));Assert.That(call.OpCode,Is.EqualTo(OpCode.Nop));
        Assert.That(call.Operands,Is.Empty);Assert.That(serial,Is.EqualTo(100+lanes));
        for(var n=0;n<lanes;n++)
        {
            var store=block.Instructions[n];Assert.That(store.OpCode,Is.EqualTo(OpCode.Move));
            Assert.That(store.NativeWriteSize,Is.EqualTo(4));
            var memory=(MemoryOperand)store.Operands[0];
            Assert.That(memory.Base,Is.EqualTo(args[0]));Assert.That(memory.Addend,Is.EqualTo(n*4));
            Assert.That(store.Operands[1],Is.EqualTo(args[8+n]));
        }
    }
}
