using System.Reflection;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedConstantFieldStoreTests
{
    private static (InjectedTypeAnalysisContext Owner,LocalVariable Receiver,Instruction Store) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","Packed",
            app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var first=owner.InjectFieldContext("First",app.SystemTypes.SystemInt32Type,FieldAttributes.Public);first.Offset=16;
        var second=owner.InjectFieldContext("Second",app.SystemTypes.SystemInt32Type,FieldAttributes.Public);second.Offset=20;
        var receiver=new LocalVariable("object",new Register(null,"X0"),owner);
        return (owner,receiver,new Instruction(0,OpCode.Move,new FieldReference(first,receiver,16),new Immediate(0x800000010))
            {NativeWriteSize=8});
    }

    [Test]
    public void ActualNativeCriAtomPackedStoreRetainsBothInt32Fields()
    {
        var (_,receiver,store)=Fixture();var pieces=PackedConstantFieldStoreRecovery.Split(store)!;
        Assert.That(pieces.Count,Is.EqualTo(2));
        Assert.That(pieces.Select(p=>p.Value.Value),Is.EqualTo(new long[]{16,8}));
        Assert.That(pieces.Select(p=>p.Width),Is.EqualTo(new[]{4,4}));
        Assert.That(pieces.All(p=>ReferenceEquals(p.Field.Local,receiver)),Is.True);
        Assert.That(store.NativeWriteSize,Is.EqualTo(8)); // planning is nonmutating
    }

    [TestCase("padding")]
    [TestCase("overlap")]
    [TestCase("partial")]
    [TestCase("reference")]
    [TestCase("unknown-width")]
    [TestCase("nested")]
    public void UnprovedByteCoverageIsNeverSplit(string failure)
    {
        var (owner,_,store)=Fixture();
        if(failure=="padding")owner.Fields[1].Offset=24;
        if(failure=="overlap")owner.Fields[1].Offset=16;
        if(failure=="partial")owner.Fields[1].Offset=22;
        if(failure=="reference")owner.Fields[1].FieldType=owner.AppContext.SystemTypes.SystemObjectType;
        if(failure=="unknown-width")store.NativeWriteSize=0;
        if(failure=="nested")((FieldReference)store.Operands[0]).Parent=(FieldReference)store.Operands[0];
        Assert.That(PackedConstantFieldStoreRecovery.Split(store),Is.Null);
    }

    [Test]
    public void SignedFieldBitsAreNotConvertedAsUnsignedNumbers()
    {
        var (_,_,store)=Fixture();store.SetOperand(1,new Immediate(unchecked((long)0xfffffffeffffffffUL)));
        var pieces=PackedConstantFieldStoreRecovery.Split(store)!;
        Assert.That(pieces.Select(p=>p.Value.Value),Is.EqualTo(new long[]{-1,-2}));
    }

    [TestCase("inherited-reference",true)] [TestCase("inherited-float",true)]
    [TestCase("inherited-intptr",true)] [TestCase("base-first-field",true)]
    [TestCase("overlapping-base-reference",false)] [TestCase("overlapping-base-integer",false)]
    [TestCase("negative-base-offset",false)] [TestCase("cyclic-base",false)]
    [TestCase("covered-float",false)] [TestCase("unknown-base-extent",false)]
    public void InheritedClassesRequireCompleteDisjointStorageAndIntegralByteCoverage(string shape,bool expected)
    {
        var (owner,receiver,store)=Fixture();var types=owner.AppContext.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(owner.DeclaringAssembly,"Test","Parent",types.SystemObjectType,TypeAttributes.Public);
        owner.BaseType=parent;
        var first=owner.Fields[0];var second=owner.Fields[1];first.Offset=24;second.Offset=28;
        store.SetOperand(0,new FieldReference(first,receiver,24));
        var beforeType=shape=="inherited-float"?types.SystemSingleType:shape=="inherited-intptr"
            ?types.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.IntPtr")!:types.SystemObjectType;
        var before=parent.InjectFieldContext("Before",beforeType,FieldAttributes.Public);before.Offset=16;
        if(shape=="base-first-field")
        {
            owner.Fields.Remove(first);first=parent.InjectFieldContext("InheritedFirst",types.SystemInt32Type,FieldAttributes.Public);
            first.Offset=24;store.SetOperand(0,new FieldReference(first,receiver,24));
        }
        if(shape=="overlapping-base-reference")before.Offset=20;
        if(shape=="overlapping-base-integer"){before.FieldType=types.SystemInt32Type;before.Offset=26;}
        if(shape=="negative-base-offset")before.Offset=-1;
        if(shape=="cyclic-base")parent.BaseType=owner;
        if(shape=="covered-float")second.FieldType=types.SystemSingleType;
        if(shape=="unknown-base-extent")before.FieldType=new InjectedTypeAnalysisContext(owner.DeclaringAssembly,
            "Test","UnknownValue",types.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.ValueType"),TypeAttributes.Public);
        var pieces=PackedConstantFieldStoreRecovery.Split(store);
        Assert.That(pieces!=null,Is.EqualTo(expected));
        if(expected)
        {
            var proven=pieces!;
            Assert.That(proven.Select(p=>p.Value.Value),Is.EqualTo(new long[]{16,8}));
            Assert.That(proven.Select(p=>p.Field.Field),Is.EqualTo(new[]{first,second}));
            Assert.That(proven.All(p=>ReferenceEquals(p.Field.Local,receiver)),Is.True);
        }
    }
}
