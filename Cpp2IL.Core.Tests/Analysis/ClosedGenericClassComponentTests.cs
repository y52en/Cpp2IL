using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClosedGenericClassComponentTests
{
    [TestCase("UnityEngine.Vector2",8,0,"x",false)] [TestCase("UnityEngine.Vector2",8,4,"y",false)]
    [TestCase("UnityEngine.Vector3",12,0,"x",false)] [TestCase("UnityEngine.Vector3",12,8,"z",false)]
    [TestCase("UnityEngine.Vector4",16,4,"y",false)] [TestCase("UnityEngine.Vector4",16,12,"w",false)]
    [TestCase("UnityEngine.Vector2",8,4,"y",true)] [TestCase("UnityEngine.Vector3",12,8,"z",true)]
    public void PartialLoadsAndStoresUseProvenConcreteValueFieldRanges(string name,int size,int component,string leaf,bool inherited)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var value=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName==name);
        var definition=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test","Pair",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,definition);
        definition.GenericParameters.Add(parameter);
        definition.InjectFieldContext("First",parameter,FieldAttributes.Public);
        definition.InjectFieldContext("Second",parameter,FieldAttributes.Public);
        var original=definition.Fields.Select(f=>f.Offset).ToArray();
        var closed=new GenericInstanceTypeAnalysisContext(definition,[value]);
        var receiverType=inherited?new InjectedTypeAnalysisContext(definition.DeclaringAssembly,"Test","Leaf",closed,TypeAttributes.Public)
            :(TypeAnalysisContext)closed;
        if(inherited)((InjectedTypeAnalysisContext)receiverType).InjectFieldContext("Tail",app.SystemTypes.SystemInt32Type,FieldAttributes.Public).Offset=16+2*size;
        var root=new LocalVariable("this",new(null,"X0"),receiverType);
        foreach(var member in new[]{(Offset:16,Name:"First"),(Offset:16+size,Name:"Second")})
        foreach(var store in new[]{false,true})
        {
            var memory=new MemoryOperand(root,addend:member.Offset+component);
            var scalar=new LocalVariable("scalar",new(null,"V0"),app.SystemTypes.SystemSingleType);
            var operation=store?new Instruction(0,OpCode.Move,memory,scalar){NativeWriteSize=4}
                :new Instruction(0,OpCode.Move,scalar,memory){NativeReadSize=4};
            var method=new InjectedMethodAnalysisContext(closed,"Test",app.SystemTypes.SystemVoidType,MethodAttributes.Public,[])
                {ControlFlowGraph=new([operation,new(1,OpCode.Return)])};
            Assert.That(MetadataResolver.ResolveFieldOffsets(method),Is.True);
            var access=operation.Operands[store?0:1] as FieldReference;
            Assert.That(access?.Field.Name,Is.EqualTo(leaf));
            Assert.That(access?.Parent?.Field.Name,Is.EqualTo(member.Name));
            Assert.That(access?.Parent?.Field.DeclaringType,Is.SameAs(closed));
            // FieldReference offsets are relative to EACH parent storage.
            Assert.That(access?.Offset,Is.EqualTo(component));
            Assert.That(access?.Parent?.Offset,Is.EqualTo(member.Offset));
            Assert.That(access!.Offset+access.Parent!.Offset,Is.EqualTo(member.Offset+component));
            Assert.That(access?.Local,Is.SameAs(root));
        }
        Assert.That(definition.Fields.Select(f=>f.Offset),Is.EqualTo(original));
    }

    [TestCase("partial-reference")] [TestCase("cross-field")]
    [TestCase("open")] [TestCase("explicit-layout")] [TestCase("reference-slot")]
    public void UnsupportedRangesDoNotBecomeComponents(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var definition=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Wrapper",t.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,definition);
        definition.GenericParameters.Add(parameter);
        definition.InjectFieldContext("Value",parameter,FieldAttributes.Public);
        definition.InjectFieldContext("Next",t.SystemInt32Type,FieldAttributes.Public);
        var value=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="UnityEngine.Vector2");
        var argument=shape=="partial-reference"?t.SystemObjectType:shape=="open"?parameter:value;
        var closed=new GenericInstanceTypeAnalysisContext(definition,[argument]);
        if(shape=="explicit-layout")definition.Attributes=TypeAttributes.Public|TypeAttributes.ExplicitLayout;
        var root=new LocalVariable("this",new(null,"X0"),shape=="reference-slot"?new ByRefTypeAnalysisContext(closed):closed);
        Assert.That(NestedFieldAccess.Find(closed,root,shape=="cross-field"?20:16,shape=="cross-field"?8:4),Is.Null);
    }
}
