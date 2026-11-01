using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateClassInitRecoveryTests
{
    [TestCase(false)] [TestCase(true)]
    public void CachedBatchMatchesFreshDefinitionsAfterEachSuccessfulRemoval(bool callbackInSecondRegion)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var metadata=new RuntimeClassTypeAnalysisContext(types.SystemObjectType,types.SystemObjectType.DeclaringAssembly);
        ISILControlFlowGraph Build()
        {
            var code=new List<Instruction>();
            for(var n=0;n<2;n++)
            {
                var klass=new LocalVariable("klass"+n,new Register(null,"klass"+n),metadata);
                var bit=new LocalVariable("bit"+n,new Register(null,"bit"+n));
                var flag=new LocalVariable("flag"+n,new Register(null,"flag"+n),types.SystemBooleanType);
                var result=new LocalVariable("result"+n,new Register(null,"result"+n));
                var effect=new Instruction(n*20+9,OpCode.CallVoid,new StringLiteral("effect"+n));
                code.AddRange([new(n*20,OpCode.Move,klass,metadata),
                    new(n*20+1,OpCode.And,bit,new MemoryOperand(klass,addend:0x126),new Immediate(1)),
                    new(n*20+2,OpCode.CheckNotEqual,flag,bit,new Immediate(0)),
                    new(n*20+3,OpCode.ConditionalJump,effect,flag)]);
                if(n==1 && callbackInSecondRegion)code.Add(new(n*20+4,OpCode.CallVoid,new StringLiteral("callback")));
                code.AddRange([new(n*20+6,OpCode.Call,new Immediate(0x100+n*8),result,metadata),new(n*20+7,OpCode.Jump,effect),effect]);
            }
            code.Add(new(50,OpCode.Return));return new ISILControlFlowGraph(code);
        }
        var fresh=Build();var cached=Build();var before=0;
        foreach(var guard in fresh.Blocks.ToArray())if(LateClassInitRecovery.TryRecover(fresh,guard,0x126,_=>true))before++;
        var after=LateClassInitRecovery.RecoverGuards(cached,0x126,_=>true);
        Assert.That(before,Is.EqualTo(callbackInSecondRegion?1:2));Assert.That(after,Is.EqualTo(before));
        string Snapshot(ISILControlFlowGraph graph)=>string.Join("\n",graph.Blocks.Select(b=>b.ID+":"+
            string.Join(",",b.Successors.Select(s=>s.ID))+":"+string.Join(",",b.Instructions.Select(i=>i.Index+"/"+i.OpCode))));
        Assert.That(Snapshot(cached),Is.EqualTo(Snapshot(fresh)));
        Assert.That(cached.Instructions.Count(i=>i.OpCode==OpCode.CallVoid && i.Operands[0] is StringLiteral {Value:"effect0" or "effect1"}),Is.EqualTo(2));
    }

    [TestCase("valid",true)]
    [TestCase("inverted",true)]
    [TestCase("callback",false)]
    [TestCase("store",false)]
    [TestCase("unknown-helper",false)]
    [TestCase("wrong-argument",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("wrong-mask",false)]
    [TestCase("managed-receiver",false)]
    [TestCase("escaping-result",false)]
    [TestCase("escaping-address",false)]
    [TestCase("escaping-memory",false)]
    [TestCase("shared-init",false)]
    [TestCase("snapshot",true)]
    [TestCase("snapshot-wide",false)]
    [TestCase("snapshot-redefined",false)]
    public void OnlyExactRuntimeGuardAndOwnedPureHelperRegionCanDisappear(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var metadata=new RuntimeClassTypeAnalysisContext(types.SystemObjectType,types.SystemObjectType.DeclaringAssembly);
        var klass=new LocalVariable("klass",new Register(null,"klass"),shape=="managed-receiver"?types.SystemObjectType:metadata);
        var bit=new LocalVariable("bit",new Register(null,"bit"));
        var flag=new LocalVariable("flag",new Register(null,"flag"),types.SystemBooleanType);
        var inverted=new LocalVariable("inverted",new Register(null,"inverted"),types.SystemBooleanType);
        var result=new LocalVariable("result",new Register(null,"result"));
        var effect=new Instruction(9,OpCode.CallVoid,new StringLiteral("application-effect"));
        var helper=new Instruction(6,OpCode.Call,new Immediate(0x100),result,
            shape=="wrong-argument"?new Immediate(0):metadata);
        var branch=new Instruction(4,OpCode.ConditionalJump,effect,shape=="inverted"?inverted:flag);
        var instructions=new List<Instruction>{
            new(0,OpCode.Move,klass,metadata),
            new(1,OpCode.And,bit,new MemoryOperand(klass,addend:shape=="wrong-offset"?0x127:0x126),new Immediate(shape=="wrong-mask"?2:1)),
            new(2,shape=="inverted"?OpCode.CheckEqual:OpCode.CheckNotEqual,flag,bit,new Immediate(0)),
            new(3,OpCode.Not,inverted,flag),branch,helper,
            new(7,OpCode.Jump,effect),effect,new(10,OpCode.Return)};
        var cfg=new ISILControlFlowGraph(instructions);
        if(shape.StartsWith("snapshot",StringComparison.Ordinal))
        {
            var ownerBlock=cfg.Blocks.Single(b=>b.Instructions.Contains(branch));
            var maskInstruction=ownerBlock.Instructions.Single(i=>i.OpCode==OpCode.And);
            var snapshot=new LocalVariable("snapshot",new Register(null,"snapshot"),types.SystemInt32Type);
            var memory=maskInstruction.Operands[1];maskInstruction.SetOperand(1,snapshot);
            var at=ownerBlock.Instructions.IndexOf(maskInstruction);
            ownerBlock.Instructions.Insert(at,new(12,OpCode.Move,snapshot,memory){NativeReadSize=shape=="snapshot-wide"?4:1});
            if(shape=="snapshot-redefined")ownerBlock.Instructions.Insert(at+1,new(13,OpCode.Move,snapshot,new Immediate(0)));
        }
        var init=cfg.Blocks.Single(b=>b.Instructions.Contains(helper));
        if(shape=="callback")init.Instructions.Insert(0,new(11,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="store")init.Instructions.Insert(0,new(11,OpCode.Move,new MemoryOperand(addend:0x2000),new Immediate(1)));
        if(shape.StartsWith("escaping",StringComparison.Ordinal))
            effect.SetOperands(new StringLiteral("application-effect"),shape switch{
                "escaping-address"=>new AddressOf(result),"escaping-memory"=>new MemoryOperand(result),_=>result});
        var guard=cfg.Blocks.Single(b=>b.Instructions.Contains(branch));
        if(shape=="shared-init")init.Predecessors.Add(cfg.EntryBlock);
        Assert.That(LateClassInitRecovery.TryRecover(cfg,guard,0x126,_=>shape!="unknown-helper"),Is.EqualTo(expected));
        Assert.That(cfg.Instructions.Contains(helper),Is.EqualTo(!expected));
        Assert.That(cfg.Instructions.Contains(effect),Is.True);
    }

    [Test]
    public void FullNativeFingerprintRejectsEverySingleByteMutationAndPrefixes()
    {
        var bytes=Convert.FromHexString("F30F1EF8FD7B01A9FD430091F30300AAE3F6FF97689E4439C800283660D240B995150194E1031FAAE2031FAA09CF0094FD7B41A9E0030032F30742F8C0035FD6");
        Assert.That(LateClassInitRecovery.MatchesBody(bytes),Is.True);
        Assert.That(LateClassInitRecovery.MatchesBody(bytes.AsSpan(0,60)),Is.False);
        for(var i=0;i<bytes.Length;i++){
            bytes[i]^=1;Assert.That(LateClassInitRecovery.MatchesBody(bytes),Is.False);bytes[i]^=1;
        }
    }
}
