using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClosedGenericValueFieldTests
{
    [TestCase(0,4,"key")]
    [TestCase(8,8,"value")]
    [TestCase(4,4,null)] // native alignment padding
    [TestCase(0,8,null)] // key plus padding is not one field
    [TestCase(8,4,null)] // partial managed reference
    [TestCase(16,8,null)]
    [TestCase(-1,4,null)]
    public void ClosedFieldsUseTheirActualUnboxedOffsetsAndWidths(int offset,int width,string? expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var pair=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.KeyValuePair`2");
        var closed=new GenericInstanceTypeAnalysisContext(pair,[app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemObjectType]);
        var original=pair.Fields.Select(f=>f.Offset).ToArray();
        var root=new LocalVariable("root",new Register(null,"root"),closed);
        var result=NestedFieldAccess.Find(closed,root,offset,width);
        Assert.That(result?.Field.Name,Is.EqualTo(expected));
        if(result!=null)
        {
            Assert.That(result.Offset,Is.EqualTo(offset));
            Assert.That(result.Field.DeclaringType,Is.SameAs(closed));
            Assert.That(result.Field.FieldType.HasAnyGenericParameters(),Is.False);
        }
        Assert.That(pair.Fields.Select(f=>f.Offset).ToArray(),Is.EqualTo(original));
    }

    [TestCase(0,4,"key","key")]
    [TestCase(8,8,"value","key")]
    [TestCase(16,4,"value",null)]
    public void NestedClosedValuesPreserveFieldIdentityAndOuterParent(int offset,int width,string field,string? parent)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var pair=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.KeyValuePair`2");
        var inner=new GenericInstanceTypeAnalysisContext(pair,[app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemObjectType]);
        var outer=new GenericInstanceTypeAnalysisContext(pair,[inner,app.SystemTypes.SystemInt32Type]);
        var root=new LocalVariable("root",new Register(null,"root"),outer);
        var result=NestedFieldAccess.Find(outer,root,offset,width);
        Assert.That(result,Is.Not.Null);
        Assert.That(result!.Field.Name,Is.EqualTo(field));
        Assert.That(result.Parent?.Field.Name,Is.EqualTo(parent));
    }

    [Test]
    public void OpenOrExplicitGenericFieldsNeverReceiveGuessedNativeOffsets()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var pair=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.KeyValuePair`2");
        var open=new GenericInstanceTypeAnalysisContext(pair,pair.GenericParameters);
        var closed=new GenericInstanceTypeAnalysisContext(pair,[app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemObjectType]);
        var original=pair.OverrideAttributes;
        try
        {
            Assert.That(NestedFieldAccess.Find(open,new("open",new(null,"open"),open),8,8),Is.Null);
            pair.OverrideAttributes=(pair.Attributes&~TypeAttributes.LayoutMask)|TypeAttributes.ExplicitLayout;
            Assert.That(NestedFieldAccess.Find(closed,new("closed",new(null,"closed"),closed),8,8),Is.Null);
        }
        finally{pair.OverrideAttributes=original;}
    }

    [TestCase(8,8,true)]
    [TestCase(8,4,false)]
    [TestCase(0,8,false)]
    [TestCase(4,4,false)]
    public void MetadataResolutionNeverFallsBackToAnObjectHeaderForClosedValueStorage(int offset,int width,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var pair=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.Generic.KeyValuePair`2");
        var closed=new GenericInstanceTypeAnalysisContext(pair,[app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemObjectType]);
        var root=new LocalVariable("root",new Register(null,"root"),closed);
        var result=new LocalVariable("result",new Register(null,"result"));
        var load=new Instruction(0,OpCode.Move,result,new MemoryOperand(root,addend:offset)){NativeReadSize=width};
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Read",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]){ControlFlowGraph=new ISILControlFlowGraph([load,new(1,OpCode.Return)])};
        Assert.That(MetadataResolver.ResolveFieldOffsets(method),Is.EqualTo(expected));
        Assert.That(load.Operands[1] is FieldReference,Is.EqualTo(expected));
        if(expected)Assert.That(((FieldReference)load.Operands[1]).Field.Name,Is.EqualTo("value"));
    }

    [TestCase("pair",0,8,true)]
    [TestCase("pair-byref",0,8,true)]
    [TestCase("enumerator",8,8,true)]
    [TestCase("enumerator-byref",8,8,true)]
    [TestCase("enumerator",4,8,false)]
    [TestCase("enumerator",0,8,false)]
    [TestCase("enumerator",16,8,false)]
    [TestCase("enumerator",8,4,false)]
    public void PackedClosedValueStoresSplitOnlyCompleteAdjacentIntegralFields(string shape,int offset,int width,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var pair=shape.StartsWith("pair",System.StringComparison.Ordinal);
        var definition=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName==
            (pair?"System.Collections.Generic.KeyValuePair`2":"System.Collections.Generic.List`1+Enumerator"));
        var closed=new GenericInstanceTypeAnalysisContext(definition,pair
            ?[app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemInt32Type]
            :[app.SystemTypes.SystemObjectType]);
        var root=new LocalVariable("root",new Register(null,"root"),shape.EndsWith("byref",System.StringComparison.Ordinal)
            ?new ByRefTypeAnalysisContext(closed):closed);
        var instruction=new Instruction(0,OpCode.Move,new MemoryOperand(root,addend:offset),
            new Immediate(unchecked((long)0xffffffff00000001UL))){NativeWriteSize=width};
        var before=definition.Fields.Select(f=>f.Offset).ToArray();
        var pieces=PackedConstantFieldStoreRecovery.Split(instruction);
        Assert.That(pieces!=null,Is.EqualTo(expected));
        if(pieces!=null)
        {
            Assert.That(pieces.Select(p=>p.Field.Field.Name),Is.EqualTo(pair?new[]{"key","value"}:new[]{"index","version"}));
            Assert.That(pieces.Select(p=>p.Value.Value),Is.EqualTo(new long[]{1,-1}));
            Assert.That(pieces.Select(p=>p.Field.Offset),Is.EqualTo(new[]{offset,offset+4}));
        }
        Assert.That(definition.Fields.Select(f=>f.Offset),Is.EqualTo(before));
    }
}
