using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class AddressedStackFieldStoreRecoveryTests
{
    [TestCase(0L,false,false,true)]
    [TestCase(0x100L,false,false,true)]
    [TestCase(0x101L,true,false,true)]
    [TestCase(0x102L,false,false,false)]
    [TestCase(0x100L,false,true,false)]
    public void ExactRefContractSplitsPackedBooleansWithoutInventingWholeInitialization(long bits,bool indirect,bool interveningCall,bool expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","PackedFlags",t.SystemValueTypeType,TypeAttributes.Public);
        type.InjectFieldContext("first",t.SystemBooleanType,FieldAttributes.Public).Offset=0;
        type.InjectFieldContext("second",t.SystemBooleanType,FieldAttributes.Public).Offset=1;
        var root=new Register(700,"stack_-40");var source=new Register(9,"X9");
        var store=new Instruction(3,OpCode.Move,root,indirect?source:new Immediate(bits)){NativeWriteSize=2};
        var list=new System.Collections.Generic.List<Instruction>{new(0,OpCode.Move,new Register(0,"X0"),new AddressOf(root))};
        if(indirect)list.Add(new(1,OpCode.Or,source,new Immediate(0),new Immediate(bits)));
        else if(interveningCall)list.Add(new(1,OpCode.Move,source,new Immediate(bits)));
        if(interveningCall){list.Add(new(2,OpCode.CallVoid,new Immediate(123)));store.SetOperand(1,source);}
        list.Add(store);list.Add(new(4,OpCode.Return));var graph=new ISILControlFlowGraph(list);
        Assert.That(AddressedStackFieldStoreRecovery.Recover(graph,[(root,type)]),Is.EqualTo(expected?1:0));
        Assert.That(graph.Instructions.Any(i=>i.Operands.Any(o=>o is DefaultStructValue)),Is.False);
        if(expected)
        {
            var stores=graph.Instructions.Where(i=>i.Destination is MemoryOperand).ToArray();
            Assert.That(stores.Length,Is.EqualTo(2));
            Assert.That(stores.All(i=>i.NativeWriteSize==1),Is.True);
            Assert.That(((Immediate)stores[0].Operands[1]).Value,Is.EqualTo(bits&255));
            Assert.That(((Immediate)stores[1].Operands[1]).Value,Is.EqualTo((bits>>8)&255));
        }
        else Assert.That(store.Operands[0],Is.TypeOf<Register>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void PackedIntegerPiecesRetainSignedness(bool indirect)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","SignedPair",t.SystemValueTypeType,TypeAttributes.Public);
        type.InjectFieldContext("signed",t.SystemInt32Type,FieldAttributes.Public).Offset=0;
        type.InjectFieldContext("unsigned",t.SystemUInt32Type,FieldAttributes.Public).Offset=4;
        var root=new Register(700,"stack_-40");var source=new Register(9,"X9");
        var bits=new Immediate(0x00000002FFFFFFFFL);
        var store=new Instruction(2,OpCode.Move,root,indirect?source:bits){NativeWriteSize=8};
        var graph=new ISILControlFlowGraph([new(0,OpCode.Move,new Register(0,"X0"),new AddressOf(root)),
            new(1,OpCode.Move,source,bits),store,new(3,OpCode.Return)]);
        Assert.That(AddressedStackFieldStoreRecovery.Recover(graph,[(root,type)]),Is.EqualTo(1));
        var stores=graph.Instructions.Where(i=>i.Destination is MemoryOperand).ToArray();
        Assert.That(((Immediate)stores[0].Operands[1]).Value,Is.EqualTo(-1));
        Assert.That(((Immediate)stores[1].Operands[1]).Value,Is.EqualTo(2));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ExactNativeMetadataVectorFieldStoresRetainNestedScalarEffect(bool includeGap)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="UnityEngine.Vector3");
        var type=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","NestedConfig",t.SystemValueTypeType,TypeAttributes.Public);
        type.InjectFieldContext("vector",vector,FieldAttributes.Public).Offset=includeGap?4:0;
        var root=new Register(700,"stack_-40");
        var store=new Instruction(1,OpCode.Move,root,new Immediate(0)){NativeWriteSize=8};
        var graph=new ISILControlFlowGraph([new(0,OpCode.Move,new Register(0,"X0"),new AddressOf(root)),store,new(2,OpCode.Return)]);
        Assert.That(AddressedStackFieldStoreRecovery.Recover(graph,[(root,type)]),Is.EqualTo(includeGap?0:1));
        if(!includeGap)
        {
            var stores=graph.Instructions.Where(i=>i.Destination is MemoryOperand).ToArray();
            Assert.That(stores.Length,Is.EqualTo(2));
            Assert.That(stores.All(i=>i.NativeWriteSize==4 && i.Operands[1] is FloatLiteral {Value:0}),Is.True);
        }
    }

    [TestCase("valid",2)]
    [TestCase("width-mismatch",0)]
    [TestCase("unknown-width",0)]
    [TestCase("no-address",0)]
    [TestCase("no-initializer",0)]
    [TestCase("overlap",0)]
    [TestCase("outside",0)]
    [TestCase("ambiguous-type",0)]
    [TestCase("non-stack",0)]
    [TestCase("explicit-layout",0)]
    public void OnlyProvenScalarFieldStoresBecomeAggregateMemoryEffects(string shape,int expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Config",t.SystemValueTypeType,
            TypeAttributes.Public|(shape=="explicit-layout"?TypeAttributes.ExplicitLayout:TypeAttributes.SequentialLayout));
        type.Fields.Add(new InjectedFieldAnalysisContext("first",t.SystemBooleanType,FieldAttributes.Public,type){Offset=0});
        type.Fields.Add(new InjectedFieldAnalysisContext("second",t.SystemBooleanType,FieldAttributes.Public,type){Offset=shape=="overlap"?0:1});
        var root=new Register(700,shape=="non-stack"?"X7":"stack_-34");
        var first=new Instruction(2,OpCode.Move,root,new Register(1,"X1")){NativeWriteSize=shape=="width-mismatch"?2:shape=="unknown-width"?0:1};
        var second=new Instruction(3,OpCode.Move,new Register(701,shape=="outside"?"stack_-30":"stack_-33"),new Register(2,"X2"))
            {NativeWriteSize=shape=="width-mismatch"?2:shape=="unknown-width"?0:1};
        if(shape=="outside")first.SetOperand(0,new Register(702,"stack_-20"));
        if(shape=="overlap")second.SetOperand(0,root);
        var graph=new ISILControlFlowGraph([new(0,OpCode.Move,root,new DefaultStructValue(type)),
            new(1,OpCode.Move,new Register(0,"X0"),new AddressOf(root)),first,second,new(4,OpCode.Return)]);
        if(shape=="no-address"){graph.Instructions[1].OpCode=OpCode.Nop;graph.Instructions[1].SetOperands();}
        if(shape=="no-initializer"){graph.Instructions[0].OpCode=OpCode.Nop;graph.Instructions[0].SetOperands();}
        if(shape=="ambiguous-type")
        {
            var other=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Other",t.SystemValueTypeType,TypeAttributes.Public);
            graph.EntryBlock.Instructions.Add(new(5,OpCode.Move,root,new DefaultStructValue(other)));
        }
        Assert.That(AddressedStackFieldStoreRecovery.Recover(graph),Is.EqualTo(expected));
        if(expected>0)
        {
            Assert.That(first.Operands[0],Is.TypeOf<MemoryOperand>());
            Assert.That(((MemoryOperand)second.Operands[0]).Addend,Is.EqualTo(1));
            Assert.That(AddressedStackFieldStoreRecovery.Recover(graph),Is.Zero);
            SsaForm.Build(graph,new DominatorInfo(graph));
            Assert.That(((Register)((MemoryOperand)first.Operands[0]).Base!).Version,Is.EqualTo(-1));
        }
        else Assert.That(first.Operands[0],Is.TypeOf<Register>());
    }
}
