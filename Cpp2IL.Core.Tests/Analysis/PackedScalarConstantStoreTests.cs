using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedScalarConstantStoreTests
{
    [TestCase(0u)] [TestCase(0x80000000u)] [TestCase(0x3f000000u)] [TestCase(0xbf800000u)]
    [TestCase(0x00000001u)] [TestCase(0x007fffffu)] [TestCase(0x7f7fffffu)]
    public void IntegerAndFiniteFloatLanesKeepExactBits(uint floatingBits)
    {
        var (method,store)=Fixture("mixed",((ulong)floatingBits<<32)|60000);
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method),Is.EqualTo(1));
        var writes=method.ControlFlowGraph!.Instructions.Where(i=>i.NativeWriteSize>0).ToArray();
        Assert.That(writes.Length,Is.EqualTo(2));
        Assert.That(((Immediate)writes[0].Operands[1]).Value,Is.EqualTo(60000));
        Assert.That(unchecked((uint)BitConverter.SingleToInt32Bits(((FloatLiteral)writes[1].Operands[1]).Value)),Is.EqualTo(floatingBits));
        Assert.That(writes.All(i=>i.NativeWriteSize==4&&i.Operands[0] is FieldReference),Is.True);
        Assert.That(store.Operands[0],Is.TypeOf<FieldReference>());
    }

    [TestCase("class-memory")] [TestCase("class-field")] [TestCase("signed")] [TestCase("bool")]
    public void OrdinaryIntegralPartitionsRemainTyped(string shape)
    {
        var (method,_)=Fixture(shape,shape=="bool"?0x0100010001000100UL:0xfffffffeffffffffUL);
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method),Is.EqualTo(1));
        var values=method.ControlFlowGraph!.Instructions.Where(i=>i.NativeWriteSize>0).Select(i=>(Immediate)i.Operands[1]).ToArray();
        if(shape=="signed")Assert.That(values.Select(v=>v.Value),Is.EqualTo(new long[]{-1,-2}));
        if(shape=="bool")Assert.That(values.All(v=>v.Value is 0 or 1),Is.True);
    }

    [TestCase("gap")] [TestCase("overlap")] [TestCase("reference")] [TestCase("unknown-root")]
    [TestCase("indexed")] [TestCase("negative")] [TestCase("partial")] [TestCase("wrong-op")]
    [TestCase("read-and-write")] [TestCase("nan")] [TestCase("infinity")] [TestCase("invalid-bool")]
    public void EveryValueAndWholePartitionMustPassBeforeMutation(string shape)
    {
        var (method,store)=Fixture(shape,shape=="nan"?0x7fc0000100000000UL:shape=="infinity"?0x7f80000000000000UL:
            shape=="invalid-bool"?0x0200000000000000UL:1UL);
        var operands=store.Operands.ToArray();var count=method.ControlFlowGraph!.Instructions.Count();
        Assert.That(PackedScalarConstantStoreRecovery.Recover(method),Is.Zero);
        Assert.That(store.Operands,Is.EqualTo(operands));
        Assert.That(method.ControlFlowGraph.Instructions.Count(),Is.EqualTo(count));
    }

    private static (InjectedMethodAnalysisContext,Instruction) Fixture(string shape,ulong bits)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","PackedConstants",t.SystemObjectType,TypeAttributes.Public);
        var bytes=shape is "bool" or "invalid-bool";var width=bytes?1:4;
        for(var i=0;i<8/width;i++)owner.InjectFieldContext("f"+i,
            bytes?t.SystemBooleanType:i==1&&shape is "mixed" or "nan" or "infinity"?t.SystemSingleType:t.SystemInt32Type,FieldAttributes.Public).Offset=16+i*width;
        if(shape=="gap")owner.Fields[1].Offset=24;
        if(shape=="overlap")owner.Fields[1].Offset=16;
        if(shape=="reference")owner.Fields[1].FieldType=t.SystemObjectType;
        var root=new LocalVariable("self",new Register(null,"X0"),shape=="unknown-root"?null:owner);
        IOperand address=shape=="class-field"?new FieldReference(owner.Fields[0],root,16):
            new MemoryOperand(root,addend:shape=="negative"?-1:16,indexRegister:shape=="indexed"?new Immediate(0):null);
        var store=new Instruction(0,shape=="wrong-op"?OpCode.Add:OpCode.Move,address,new Immediate(unchecked((long)bits)))
            {NativeWriteSize=shape=="partial"?4:8,NativeReadSize=shape=="read-and-write"?8:0};
        var instructions=new System.Collections.Generic.List<Instruction>{store,new(1,OpCode.Return)};
        var method=new InjectedMethodAnalysisContext(owner,"Caller",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new(instructions),Locals=[root],ParameterLocals=[root]};
        return (method,store);
    }
}
