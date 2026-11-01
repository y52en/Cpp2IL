using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedPrimitiveFieldCopyTests
{
    [TestCase("byte",4)] [TestCase("char",4)] [TestCase("boolean",8)] [TestCase("int16",8)]
    [TestCase("int32",8)] [TestCase("single",8)] [TestCase("single",16)] [TestCase("double",16)]
    public void TypedMetadataLanesSupportDifferentPackedWidths(string scalar,int width)=>Check("ordinary",scalar,width,true);

    [TestCase("field-load",true)] [TestCase("field-store",true)] [TestCase("multiple-stores",true)]
    [TestCase("overlap",true)] [TestCase("mixed",true)]
    [TestCase("unknown-source",false)] [TestCase("unknown-target",false)] [TestCase("gap",false)]
    [TestCase("overlapping-layout",false)] [TestCase("different-type",false)] [TestCase("arithmetic",false)]
    [TestCase("return-value",false)] [TestCase("address-escape",false)] [TestCase("incoming-parameter",false)]
    [TestCase("duplicate-definition",false)] [TestCase("wrong-store-width",false)] [TestCase("indexed-source",false)]
    [TestCase("negative-offset",false)] [TestCase("overflow-offset",false)] [TestCase("non-dominating",false)]
    [TestCase("partial-read",false)] [TestCase("source-is-payload",false)] [TestCase("target-is-payload",false)]
    [TestCase("reference-lanes",false)] [TestCase("cyclic-field-path",false)]
    public void EveryByteAndEveryConsumerMustBeProvenBeforeAnyMutation(string shape,bool expected)=>Check(shape,"int32",8,expected);

    private static void Check(string shape,string scalar,int width,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var fieldType=scalar switch {"byte"=>t.SystemByteType,"char"=>t.SystemCharType,"boolean"=>t.SystemBooleanType,
            "int16"=>t.SystemInt16Type,"single"=>t.SystemSingleType,"double"=>t.SystemDoubleType,_=>t.SystemInt32Type};
        if(shape=="reference-lanes")fieldType=t.SystemStringType;
        var laneWidth=scalar switch {"byte" or "boolean"=>1,"char" or "int16"=>2,"double"=>8,_=>4};
        var sourceOwner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","PackedSource",t.SystemObjectType,TypeAttributes.Public);
        var targetOwner=new InjectedTypeAnalysisContext(sourceOwner.DeclaringAssembly,"Test","PackedTarget",t.SystemObjectType,TypeAttributes.Public);
        var laneCount=width/laneWidth;
        for(var n=0;n<laneCount+(shape=="overlap"?1:0);n++)
        {
            var type=shape=="mixed"&&n==1?t.SystemSingleType:fieldType;
            sourceOwner.InjectFieldContext("s"+n,type,FieldAttributes.Public).Offset=16+n*laneWidth;
            targetOwner.InjectFieldContext("d"+n,shape=="different-type"?t.SystemUInt32Type:type,FieldAttributes.Public).Offset=16+n*laneWidth;
        }
        if(shape=="gap")targetOwner.Fields[1].Offset+=laneWidth;
        if(shape=="overlapping-layout")sourceOwner.Fields[1].Offset=16;
        var source=new LocalVariable("source",new Register(1,"X1"),shape=="unknown-source"?null:sourceOwner);
        var target=shape=="overlap"?source:new LocalVariable("target",new Register(2,"X2"),shape=="unknown-target"?null:targetOwner);
        var chunk=new LocalVariable("bits",new Register(3,"X3"),t.SystemInt64Type);
        var other=new LocalVariable("other",new Register(4,"X4"),t.SystemInt64Type);
        IOperand read=shape=="field-load"?new FieldReference(sourceOwner.Fields[0],source,16):new MemoryOperand(
            shape=="source-is-payload"?chunk:source,
            shape=="indexed-source"?new Immediate(1):null,
            addend:shape=="negative-offset"?-1:shape=="overflow-offset"?long.MaxValue:16);
        if(shape=="cyclic-field-path")
        {var cycle=new FieldReference(sourceOwner.Fields[0],source,16);cycle.Parent=cycle;read=cycle;}
        IOperand write=shape=="field-store"?new FieldReference(targetOwner.Fields[0],target,16):new MemoryOperand(
            shape=="target-is-payload"?chunk:target,addend:shape=="overlap"?20:16);
        var load=new Instruction(0,OpCode.Move,chunk,read){NativeReadSize=shape=="partial-read"?2:width};
        var store=new Instruction(1,OpCode.Move,write,chunk){NativeWriteSize=shape=="wrong-store-width"?4:width};
        var instructions=new System.Collections.Generic.List<Instruction>{load,store,new(2,OpCode.Return)};
        if(shape=="multiple-stores")instructions.Insert(2,new(3,OpCode.Move,new MemoryOperand(target,addend:16),chunk){NativeWriteSize=width});
        if(shape=="duplicate-definition")instructions.Insert(1,new(3,OpCode.Move,chunk,new Immediate(1)));
        if(shape=="arithmetic")instructions.Insert(1,new(3,OpCode.Add,other,chunk,new Immediate(1)));
        if(shape=="return-value")instructions[^1]=new(2,OpCode.Return,chunk);
        if(shape=="address-escape")instructions.Insert(1,new(3,OpCode.CallVoid,new StringLiteral("observe"),new AddressOf(chunk)));
        if(shape=="non-dominating")instructions.Insert(0,new(3,OpCode.ConditionalJump,store,new Immediate(1)));
        var caller=new InjectedMethodAnalysisContext(sourceOwner,"Copy",t.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[])
        {
            ControlFlowGraph=new(instructions),Locals=[source,target,chunk,other],
            ParameterLocals=shape=="incoming-parameter"?[source,target,chunk]:[source,target]
        };
        var oldLocals=caller.Locals.Count;
        Assert.That(PackedPrimitiveFieldCopyRecovery.Recover(caller),Is.EqualTo(expected?1:0));
        if(!expected)
        {Assert.That(load.OpCode,Is.EqualTo(OpCode.Move));Assert.That(store.OpCode,Is.EqualTo(OpCode.Move));Assert.That(caller.Locals.Count,Is.EqualTo(oldLocals));return;}
        Assert.That(load.OpCode,Is.EqualTo(OpCode.Nop));Assert.That(store.OpCode,Is.EqualTo(OpCode.Nop));
        var reads=caller.ControlFlowGraph.Instructions.Where(i=>i.NativeReadSize>0).ToArray();
        var writes=caller.ControlFlowGraph.Instructions.Where(i=>i.NativeWriteSize>0).ToArray();
        Assert.That(reads.Length,Is.EqualTo(laneCount));Assert.That(writes.Length,Is.EqualTo(laneCount*(shape=="multiple-stores"?2:1)));
        Assert.That(reads.All(i=>i.NativeReadSize==laneWidth&&i.Operands[1] is FieldReference),Is.True);
        Assert.That(writes.All(i=>i.NativeWriteSize==laneWidth&&i.Operands[0] is FieldReference),Is.True);
        var ordered=caller.ControlFlowGraph.Instructions.ToArray();
        Assert.That(reads.Max(i=>System.Array.IndexOf(ordered,i)),Is.LessThan(writes.Min(i=>System.Array.IndexOf(ordered,i))));
        foreach(var writeInstruction in writes)
            Assert.That(reads.Any(r=>ReferenceEquals(r.Operands[0],writeInstruction.Operands[1])),Is.True);
    }
}
