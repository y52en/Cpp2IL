using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackFieldRecoveryTests
{
    private static (InjectedMethodAnalysisContext Caller,Instruction Read,LocalVariable Storage,FieldAnalysisContext Field) Fixture(bool assigned=false,bool unknown=false,bool late=false,bool conflict=false)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Data",types.SystemValueTypeType,TypeAttributes.Public);
        var field=new InjectedFieldAnalysisContext("title",types.SystemInt32Type,FieldAttributes.Public,type){Offset=12};type.Fields.Add(field);
        var writer=type.InjectMethodContext("Fill",types.SystemVoidType,MethodAttributes.Public);
        var caller=type.InjectMethodContext("Caller",types.SystemInt32Type,MethodAttributes.Public|MethodAttributes.Static);
        var storage=new LocalVariable("storage",new Register(null,"stack_-80",1),type);
        var slot=new LocalVariable("slot",new Register(null,"stack_-74"),conflict?types.SystemSingleType:types.SystemInt32Type);
        var result=new LocalVariable("result",new Register(null,"X0"),types.SystemInt32Type);
        var read=new Instruction(2,OpCode.Move,result,slot);
        var call=new Instruction(1,OpCode.CallVoid,unknown?new Immediate(0x1234):writer,new AddressOf(storage));
        var list=new List<Instruction>();
        if(assigned)list.Add(new(0,OpCode.Move,slot,new Immediate(42)));
        if(late)list.Add(read);
        list.Add(call);
        if(!late)list.Add(read);
        list.Add(new(3,OpCode.Return,result));caller.ControlFlowGraph=new(list);
        return(caller,read,storage,field);
    }

    [Test]
    public void UndefinedReadAfterKnownByAddressWriteBindsExactField()
    {
        var f=Fixture();
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.True);
        Assert.That(f.Read.Operands[1],Is.TypeOf<FieldReference>());
        var field=(FieldReference)f.Read.Operands[1];
        Assert.That(field.Field,Is.SameAs(f.Field));Assert.That(field.Local,Is.SameAs(f.Storage));
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.False);
    }

    [TestCase(true,false,false,false)]
    [TestCase(false,true,false,false)]
    [TestCase(false,false,true,false)]
    [TestCase(false,false,false,true)]
    public void UnprovedOrAlreadyAssignedReadIsUnchanged(bool assigned,bool unknown,bool late,bool conflict)
    {
        var f=Fixture(assigned,unknown,late,conflict);
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.False);
        Assert.That(f.Read.Operands[1],Is.TypeOf<LocalVariable>());
    }

    [Test]
    public void SameAddressWithTwoStorageIdentitiesIsAmbiguous()
    {
        var f=Fixture();var graph=f.Caller.ControlFlowGraph!;
        var original=graph.Instructions.Find(i=>i.IsCall)!;
        var block=graph.Blocks.Find(b=>b.Instructions.Contains(original))!;
        var other=new LocalVariable("other",new Register(null,"stack_-80",2),f.Storage.Type);
        block.Instructions.Add(new(4,OpCode.CallVoid,original.Operands[0],new AddressOf(other)));
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.False);
    }

    [Test]
    public void WholeValueAtStorageStartIsNotProjectedToFieldZero()
    {
        var f=Fixture();var slot=(LocalVariable)f.Read.Operands[1];
        slot.Register=new Register(null,"stack_-80");f.Field.Offset=0;
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.False);
    }

    [Test]
    public void WriterOnOnlyOneIncomingPathDoesNotDominateRead()
    {
        var f=Fixture();var original=f.Caller.ControlFlowGraph!.Instructions.Find(i=>i.IsCall)!;
        var graph=new ISILControlFlowGraph([]);
        var left=new Block{ID=2};var right=new Block{ID=3};var join=new Block{ID=4};
        graph.Blocks.AddRange([left,right,join]);
        graph.EntryBlock.Successors.AddRange([left,right]);left.Predecessors.Add(graph.EntryBlock);right.Predecessors.Add(graph.EntryBlock);
        left.Successors.Add(join);right.Successors.Add(join);join.Predecessors.AddRange([left,right]);
        join.Successors.Add(graph.ExitBlock);graph.ExitBlock.Predecessors.Add(join);
        left.Instructions.Add(original);join.Instructions.Add(f.Read);
        f.Caller.ControlFlowGraph=graph;
        Assert.That(StackFieldRecovery.Run(f.Caller),Is.False);
    }
}
