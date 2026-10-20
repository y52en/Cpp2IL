using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class WideReadOnlyStoreTests
{
    [TestCase("float2",true)]
    [TestCase("float4",true)]
    [TestCase("double2",true)]
    [TestCase("mixed",true)]
    [TestCase("gap",false)]
    [TestCase("overlap",false)]
    [TestCase("pointer",false)]
    [TestCase("missing-width",false)]
    [TestCase("different-width",false)]
    [TestCase("unreadable",false)]
    [TestCase("wrong-receiver",false)]
    [TestCase("partial-offset",false)]
    [TestCase("nested",false)]
    [TestCase("missing-field",false)]
    public void WholeNativeStoreRequiresCompleteExactScalarFieldCoverage(string shape,bool expected)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var owner=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","WideLiteral",
            types.SystemObjectType,TypeAttributes.Public);
        var wide=shape=="double2"?16:shape=="float4"?16:8;
        var size=shape=="double2"?8:4;
        for(var n=0;n<wide/size;n++)
        {
            var type=shape=="double2"?types.SystemDoubleType:shape=="mixed" && n==1?types.SystemInt32Type:types.SystemSingleType;
            if(shape=="pointer" && n==1)type=types.SystemObjectType;
            owner.Fields.Add(new InjectedFieldAnalysisContext("field"+n,type,FieldAttributes.Public,owner)
                {Offset=16+n*size+(shape=="gap" && n==1?1:0)});
        }
        if(shape=="overlap")owner.Fields.Add(new InjectedFieldAnalysisContext("alias",types.SystemSingleType,FieldAttributes.Public,owner){Offset=16});
        if(shape=="missing-field")owner.Fields.RemoveAt(owner.Fields.Count-1);
        var receiver=new LocalVariable("this",new Register(null,"X0"),shape=="wrong-receiver"?types.SystemObjectType:owner);
        var field=new FieldReference(owner.Fields[0],receiver,shape=="partial-offset"?17:16);
        if(shape=="nested")field.Parent=new FieldReference(owner.Fields[0],receiver,16);
        var instruction=new Instruction(0,OpCode.Move,field,new MemoryOperand(addend:0x1000))
            {NativeReadSize=shape=="missing-width"?0:shape=="different-width"?4:wide,NativeWriteSize=wide};
        var reads=0;
        bool Read(ulong address,int width,out ulong bits)
        {
            reads++;
            bits=width==8?0x8000000000000000UL:address==0x1000?0xBF800000UL:0x3F800000UL;
            return !(shape=="unreadable" && address>0x1000);
        }
        var result=ReadOnlyScalarRecovery.ProjectWideStore(instruction,Read);
        Assert.That(result!=null,Is.EqualTo(expected));
        Assert.That(instruction.Operands[0],Is.SameAs(field));
        Assert.That(instruction.Operands[1],Is.InstanceOf<MemoryOperand>());
        if(!expected)return;
        Assert.That(result!.Count,Is.EqualTo(wide/size));
        Assert.That(reads,Is.EqualTo(wide/size));
        for(var n=0;n<result.Count;n++)
        {
            Assert.That(result[n].Field.Field,Is.SameAs(owner.Fields[n]));
            Assert.That(result[n].Field.Offset,Is.EqualTo(16+n*size));
            Assert.That(result[n].Width,Is.EqualTo(size));
        }
        if(shape=="double2")Assert.That(BitConverter.DoubleToInt64Bits(((DoubleLiteral)result[0].Value).Value),Is.EqualTo(long.MinValue));
        else Assert.That(((FloatLiteral)result[0].Value).Value,Is.EqualTo(-1f));
    }
}
