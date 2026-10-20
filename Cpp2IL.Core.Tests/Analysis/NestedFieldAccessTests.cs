using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.InstructionSets;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class NestedFieldAccessTests
{
    [TestCase(8,0,true)]
    [TestCase(4,0,false)]
    [TestCase(1,0,false)]
    [TestCase(0,0,false)]
    [TestCase(8,1,false)]
    public void NestedReferenceRequiresExactPointerSlot(int width,int displacement,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var entry=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.DictionaryEntry");
        var leaf=entry.Fields.First(f=>!f.IsStatic && !f.FieldType.IsValueType);
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","EntryHolder",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        owner.InjectFieldContext("Entry",entry,FieldAttributes.Public).Offset=16;
        var root=new LocalVariable("holder",new Register(null,"X19"),owner);
        var access=NestedFieldAccess.Find(owner,root,16+leaf.Offset+displacement,width);
        Assert.That(access!=null,Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(access!.Field,Is.SameAs(leaf));
            Assert.That(access.Parent?.Field.Name,Is.EqualTo("Entry"));
            Assert.That(access.Local,Is.SameAs(root));
        }
    }

    [Test]
    public void DoesNotWalkThroughAReferenceObjectOrAcceptOverlappingStorage()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var entry=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Collections.DictionaryEntry");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","OverlapReference",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        owner.InjectFieldContext("Entry",entry,FieldAttributes.Public).Offset=16;
        owner.InjectFieldContext("Reference",app.SystemTypes.SystemObjectType,FieldAttributes.Public).Offset=16;
        Assert.That(NestedFieldAccess.Find(owner,new LocalVariable("holder",new Register(null,"X19"),owner),16,8),Is.Null);
    }

    [TestCase(Arm64Mnemonic.LDRB, Arm64Register.W0, 1)]
    [TestCase(Arm64Mnemonic.LDRSB, Arm64Register.X0, 1)]
    [TestCase(Arm64Mnemonic.LDURSH, Arm64Register.X0, 2)]
    [TestCase(Arm64Mnemonic.LDRSW, Arm64Register.X0, 4)]
    [TestCase(Arm64Mnemonic.LDPSW, Arm64Register.X0, 4)]
    [TestCase(Arm64Mnemonic.LDR, Arm64Register.S0, 4)]
    [TestCase(Arm64Mnemonic.LDR, Arm64Register.D0, 8)]
    [TestCase(Arm64Mnemonic.LDR, Arm64Register.V0, 16)]
    public void ReadWidthIsMemoryWidthNotDestinationWidth(Arm64Mnemonic mnemonic, Arm64Register register, int expected)
        => Assert.That(NewArmV8InstructionSet.ReadWidth(mnemonic,register), Is.EqualTo(expected));

    [TestCase(16,"x")]
    [TestCase(20,"y")]
    [TestCase(24,"z")]
    public void MetadataResolverUsesNativeReadWidthForNestedVector(int offset, string expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","ReadHolder",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        owner.InjectFieldContext("Vector",vector,FieldAttributes.Public).Offset=16;
        var root=new LocalVariable("holder",new Register(null,"X19"),owner);
        var method=new InjectedMethodAnalysisContext(owner,"Read",app.SystemTypes.SystemSingleType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var instruction=new Instruction(0,OpCode.Move,new LocalVariable("value",new Register(null,"V0")),new MemoryOperand(root,addend:offset)){NativeReadSize=4};
        method.ControlFlowGraph=new([instruction,new(1,OpCode.Return)]);
        Assert.That(MetadataResolver.ResolveFieldOffsets(method),Is.True);
        var field=instruction.Operands[1] as FieldReference;
        Assert.That(field?.Field.Name,Is.EqualTo(expected));
        Assert.That(field?.Parent?.Field.Name,Is.EqualTo("Vector"));
    }

    [TestCase(16,4,"x",true)]
    [TestCase(20,4,"y",true)]
    [TestCase(24,4,"z",true)]
    [TestCase(16,12,"Vector",false)]
    [TestCase(16,2,null,false)]
    [TestCase(16,0,null,false)]
    [TestCase(27,4,null,false)]
    public void WidthDistinguishesWholeVectorFromNestedScalar(int offset,int width,string? expected,bool nested)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Holder",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var field=owner.InjectFieldContext("Vector",vector,FieldAttributes.Public);field.Offset=16;
        var root=new LocalVariable("holder",new Register(null,"X19"),owner);
        var result=NestedFieldAccess.Find(owner,root,offset,width);
        Assert.That(result?.Field.Name,Is.EqualTo(expected));
        Assert.That(result?.Parent!=null,Is.EqualTo(nested));
        if(result!=null) Assert.That(result.Local,Is.SameAs(root));
    }

    [Test]
    public void OverlappingAggregateMetadataIsRejected()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Overlap",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        owner.InjectFieldContext("A",vector,FieldAttributes.Public).Offset=16;
        owner.InjectFieldContext("B",vector,FieldAttributes.Public).Offset=16;
        Assert.That(NestedFieldAccess.Find(owner,new LocalVariable("root",new Register(null,"X19"),owner),16,4),Is.Null);
    }
}
