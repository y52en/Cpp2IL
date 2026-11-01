using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class WholeStructInitializationRecoveryTests
{
    [TestCase(0)]
    [TestCase(4)]
    [TestCase(20)]
    [TestCase(64)]
    public void CollapsedTailFirstDefaultCarriesExactlyTheCompleteVerifiedExtent(int previousExtent)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","TwentyByteData",types.SystemValueTypeType,TypeAttributes.Public);
        var root=new Register(null,"stack_-80");var block=new Block();
        var tail=new Instruction(0,OpCode.Move,new Register(null,"stack_-70"),new Immediate(0))
            {NativeWriteSize=4,NativeZeroSize=previousExtent};
        var low=new Instruction(1,OpCode.Move,root,new Immediate(0)){NativeWriteSize=8,NativeZeroSize=20};
        var middle=new Instruction(2,OpCode.Move,new Register(null,"stack_-78"),new Immediate(0)){NativeWriteSize=8,NativeZeroSize=12};
        block.Instructions=[tail,low,middle];
        Assert.That(WholeStructInitializationRecovery.RecoverGroup(block,0,root,type,20),Is.True);
        Assert.That(tail.Operands[0],Is.EqualTo(root));
        Assert.That(tail.Operands[1],Is.TypeOf<DefaultStructValue>());
        Assert.That(tail.NativeWriteSize,Is.Zero);
        Assert.That(tail.NativeZeroSize,Is.EqualTo(20),"whole union, neither the first tail nor unrelated neighboring bytes");
        Assert.That(low.NativeZeroSize,Is.Zero);Assert.That(middle.NativeZeroSize,Is.Zero);
    }
    [TestCase(16,false,false,40)]
    [TestCase(8,false,false,0)]
    [TestCase(16,true,false,0)]
    [TestCase(16,false,true,0)]
    public void DeferredVectorZeroRequiresFullRegisterProofWithoutClobber(int zeroWidth,bool overwritten,bool call,int expected)
    {
        var vector=new Register(null,"V0");
        var list=new System.Collections.Generic.List<Instruction>{new(0,OpCode.Move,vector,new Immediate(0)){NativeZeroSize=zeroWidth}};
        if(overwritten)list.Add(new(1,OpCode.Move,vector,new Immediate(1)));
        if(call)list.Add(new(2,OpCode.CallVoid,new Immediate(123)));
        list.Add(new(3,OpCode.Move,new Register(null,"stack_-40"),new Immediate(0)){NativeWriteSize=8});
        list.Add(new(4,OpCode.Move,new Register(null,"stack_-50"),vector){NativeWriteSize=16});
        var root=new Instruction(5,OpCode.Move,new Register(null,"stack_-60"),vector){NativeWriteSize=16};list.Add(root);
        WholeStructInitializationRecovery.MarkZeroExtents(new ISILControlFlowGraph(list));
        Assert.That(root.NativeZeroSize,Is.EqualTo(expected));
    }

    [TestCase("ordered",24)]
    [TestCase("reordered",24)]
    [TestCase("gap",8)]
    [TestCase("nonzero",8)]
    [TestCase("call",8)]
    [TestCase("read",8)]
    [TestCase("unknown-width",8)]
    public void DeferredZeroCoverageNeverCrossesUnprovenBytesOrEffects(string shape,int expected)
    {
        var root=new Instruction(0,OpCode.Move,new Register(null,"stack_-58"),new Immediate(0)){NativeWriteSize=8};
        var middle=new Instruction(1,OpCode.Move,new Register(null,shape=="gap"?"stack_-48":"stack_-50"),new Immediate(shape=="nonzero"?1:0))
            {NativeWriteSize=shape=="unknown-width"?0:8};
        var last=new Instruction(2,OpCode.Move,new Register(null,shape=="gap"?"stack_-40":"stack_-48"),new Immediate(0)){NativeWriteSize=8};
        var list=shape=="reordered"?new System.Collections.Generic.List<Instruction>{middle,last,root}:new(){root,middle,last};
        if(shape=="call")list.Insert(1,new(3,OpCode.CallVoid,new Immediate(123)));
        if(shape=="read")list.Insert(1,new(3,OpCode.Move,new Register(null,"X0"),new Register(null,"stack_-58")));
        var graph=new ISILControlFlowGraph(list);
        WholeStructInitializationRecovery.MarkZeroExtents(graph);
        Assert.That(root.NativeZeroSize,Is.EqualTo(expected));
        Assert.That(root.Operands[1],Is.TypeOf<Immediate>(),"no managed type or initializer is invented by coverage annotation");
    }

    [TestCase("ref",true)]
    [TestCase("value",false)]
    [TestCase("objectref",false)]
    [TestCase("ambiguous",false)]
    [TestCase("raw_float_before_ref",true)]
    public void ExactMetadataReferenceParametersEstablishStructStorage(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var type=app.Assemblies.SelectMany(a=>a.Types).First(t=>t.IsValueType && TypeSizes.UnboxedSize(t,8)>16 && TypeSizes.UnboxedSize(t,8)<=128);
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","RefCalls",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var parameter=shape=="value"?type:new ByRefTypeAnalysisContext(shape=="objectref"?app.SystemTypes.SystemObjectType:type);
        var target=owner.InjectMethodContext("Consume",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,
            shape=="raw_float_before_ref"?[app.SystemTypes.SystemSingleType,parameter]:[parameter]);
        const ulong address=0xDEADBEEF;app.MethodsByAddress[address]=shape=="ambiguous"?[target,target]:[target];
        var caller=owner.InjectMethodContext("Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var root=new Register(null,"stack_-100");var instructions=new System.Collections.Generic.List<Instruction>();
        var size=(int)TypeSizes.UnboxedSize(type,8);
        for(var offset=0;offset<size;)
        {
            var width=size-offset>=8?8:1;
            instructions.Add(new Instruction(instructions.Count,OpCode.Move,new Register(null,"stack_-"+(256-offset).ToString("X")),new Immediate(0)){NativeWriteSize=width});
            offset+=width;
        }
        Instruction call;
        if(shape=="raw_float_before_ref")
        {
            instructions.Add(new(instructions.Count,OpCode.Move,new Register(null,"X0"),new AddressOf(root)));
            call=new(instructions.Count,OpCode.CallVoid,new Immediate((long)address));
            call.SetOperands(new IOperand[]{new Immediate((long)address)}.Concat(Enumerable.Range(0,8).Select(i=>(IOperand)new Register(null,"X"+i)))
                .Concat(Enumerable.Range(0,8).Select(i=>(IOperand)new Register(null,"V"+i))).ToList());
        }
        else call=new(instructions.Count,OpCode.CallVoid,new Immediate((long)address),new AddressOf(root),new Immediate(0));
        instructions.Add(call);instructions.Add(new(instructions.Count,OpCode.Return));caller.ControlFlowGraph=new(instructions);
        Assert.That(WholeStructInitializationRecovery.Run(caller),Is.EqualTo(expected));
        Assert.That(instructions[0].Operands[1] is DefaultStructValue,Is.EqualTo(expected));
    }

    [TestCase(16,false,true)]
    [TestCase(8,false,false)]
    [TestCase(0,false,false)]
    [TestCase(16,true,false)]
    public void VectorStoreRequiresFullProvenZeroWidth(int zeroWidth,bool overwritten,bool expected)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Data",types.SystemValueTypeType,TypeAttributes.Public);
        var root=new Register(null,"stack_-80");var vector=new Register(null,"V0");var block=new Block();
        block.Instructions.Add(new Instruction(0,OpCode.Move,vector,new Immediate(0)){NativeZeroSize=zeroWidth});
        if(overwritten)block.Instructions.Add(new(1,OpCode.Move,vector,new Immediate(1)));
        var first=block.Instructions.Count;
        block.Instructions.Add(new Instruction(2,OpCode.Move,root,vector){NativeWriteSize=16});
        block.Instructions.Add(new Instruction(3,OpCode.Move,new Register(null,"stack_-70"),vector){NativeWriteSize=16});
        Assert.That(WholeStructInitializationRecovery.RecoverGroup(block,first,root,type,32),Is.EqualTo(expected));
    }

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
