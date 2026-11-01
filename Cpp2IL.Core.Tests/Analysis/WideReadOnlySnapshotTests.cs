using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class WideReadOnlySnapshotTests
{
    [TestCase("valid",true)]
    [TestCase("call",false)]
    [TestCase("redefined",false)]
    [TestCase("address",false)]
    [TestCase("read-width",false)]
    [TestCase("unreadable",false)]
    [TestCase("before-load",false)]
    public void ProjectOnlyAProvenWholeImmutableLiteralLoadInTheSameCallFreeBlock(string shape,bool expected)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","FourConstants",
            types.SystemObjectType,TypeAttributes.Public);
        for(var n=0;n<4;n++)owner.Fields.Add(new InjectedFieldAnalysisContext("field"+n,types.SystemInt32Type,
            FieldAttributes.Public,owner){Offset=16+n*4});
        var receiver=new LocalVariable("this",new Register(null,"X0"),owner);
        var vector=new LocalVariable("vector",new Register(null,"V0"),types.SystemInt32Type);
        var load=new Instruction(0,OpCode.Move,vector,new MemoryOperand(addend:0x1000))
            {NativeReadSize=shape=="read-width"?4:16};
        var target=new Instruction(3,OpCode.Move,new FieldReference(owner.Fields[0],receiver,16),vector){NativeWriteSize=16};
        var instructions=new System.Collections.Generic.List<Instruction>{load,
            new(1,OpCode.Move,new LocalVariable("other",new Register(null,"X9")),new Immediate(1)),target,new(4,OpCode.Return)};
        if(shape=="call")instructions.Insert(2,new(2,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="redefined")instructions.Insert(2,new(2,OpCode.Move,vector,new Immediate(0)));
        if(shape=="address")instructions.Insert(2,new(2,OpCode.Move,new LocalVariable("alias",new Register(null,"alias")),new AddressOf(vector)));
        if(shape=="before-load"){instructions.Remove(target);instructions.Insert(0,target);}
        var cfg=new ISILControlFlowGraph(instructions);var block=cfg.Blocks.Single(b=>b.Instructions.Contains(target));
        bool Read(ulong address,int width,out ulong bits)
        {
            bits=address==0x100c?2UL:32UL;
            return shape!="unreadable" && address>=0x1000 && address<=0x100c && width==4;
        }
        var result=ReadOnlyScalarRecovery.ProjectWideSnapshot(cfg,block,target,Read);
        Assert.That(result!=null,Is.EqualTo(expected));
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(target.Operands[1],Is.SameAs(vector));
        if(expected)Assert.That(result!.Select(p=>((Immediate)p.Value).Value),Is.EqualTo(new long[]{32,32,32,2}));
    }
}
