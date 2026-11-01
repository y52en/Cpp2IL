using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MethodInfoWordValueTests
{
    [TestCase("IntPtr",true)]
    [TestCase("UIntPtr",true)]
    [TestCase("Byte",true)]
    [TestCase("SByte",true)]
    [TestCase("Int16",true)]
    [TestCase("UInt16",true)]
    [TestCase("Int32",true)]
    [TestCase("UInt32",true)]
    [TestCase("Int64",true)]
    [TestCase("UInt64",true)]
    [TestCase("Boolean",true)]
    [TestCase("Char",true)]
    [TestCase("Single",false)]
    [TestCase("Double",false)]
    [TestCase("Decimal",false)]
    [TestCase("DateTime",false)]
    [TestCase("Object",false)]
    public void OnlyCanonicalOrPrimitiveWordValuesAreSupported(string name,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System."+name)!;
        Assert.That(type,Is.Not.Null);
        Assert.That(MethodInfoTailRecovery.IsSupportedWordValue(type),Is.EqualTo(expected));
    }

    [TestCase("Byte",true)]
    [TestCase("SByte",true)]
    [TestCase("Int16",true)]
    [TestCase("UInt16",true)]
    [TestCase("Int32",true)]
    [TestCase("UInt32",true)]
    [TestCase("Int64",true)]
    [TestCase("UInt64",true)]
    [TestCase("Single",false)]
    [TestCase("Double",false)]
    [TestCase("Boolean",false)]
    [TestCase("Char",false)]
    [TestCase("IntPtr",false)]
    [TestCase("UIntPtr",false)]
    [TestCase("Object",false)]
    [TestCase(null,false)]
    public void EnumStorageMustBeExactlyOneOfTheCliIntegerTypes(string? storage,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var assembly=app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var type=new InjectedTypeAnalysisContext(assembly,"Test","WordEnum",assembly.GetTypeByFullName("System.Enum"),TypeAttributes.Public)
            {EnumUnderlyingType=storage==null?null:assembly.GetTypeByFullName("System."+storage)};
        Assert.That(MethodInfoTailRecovery.IsSupportedWordValue(type),Is.EqualTo(expected));
    }

    [Test]
    public void CyclicEnumStorageIsNeverScalar()
    {
        var app=TestGameLoader.LoadSimple2019Game();var assembly=app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var type=new InjectedTypeAnalysisContext(assembly,"Test","Cycle",assembly.GetTypeByFullName("System.Enum"),TypeAttributes.Public);
        type.EnumUnderlyingType=type;
        Assert.That(MethodInfoTailRecovery.IsSupportedWordValue(type),Is.False);
    }

    [TestCase("Byte",false)]
    [TestCase("Byte",true)]
    [TestCase("SByte",false)]
    [TestCase("SByte",true)]
    [TestCase("Int16",false)]
    [TestCase("Int16",true)]
    [TestCase("UInt16",false)]
    [TestCase("UInt16",true)]
    [TestCase("Int32",false)]
    [TestCase("Int32",true)]
    [TestCase("UInt32",false)]
    [TestCase("UInt32",true)]
    [TestCase("Int64",false)]
    [TestCase("Int64",true)]
    [TestCase("UInt64",false)]
    [TestCase("UInt64",true)]
    [TestCase("IntPtr",false)]
    [TestCase("IntPtr",true)]
    [TestCase("UIntPtr",false)]
    [TestCase("UIntPtr",true)]
    public void ProvenWordArgumentsAndReturnsKeepExactMetadataTypeAndAliasedValue(string storage,bool tail)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;var assembly=owner.DeclaringAssembly;
        var primitive=assembly.GetTypeByFullName("System."+storage)!;
        var type=storage is "IntPtr"or"UIntPtr"?primitive:
            new InjectedTypeAnalysisContext(assembly,"Test","ActualEnum",assembly.GetTypeByFullName("System.Enum"),TypeAttributes.Public){EnumUnderlyingType=primitive};
        var target=new InjectedMethodAnalysisContext(owner,"Target",type,MethodAttributes.Public|MethodAttributes.Static,[type]);
        var method=new InjectedMethodAnalysisContext(owner,"Caller",type,MethodAttributes.Public|MethodAttributes.Static,[]);
        var info=new RuntimeMethodInfoAnalysisContext(target,assembly);
        var ops=new System.Collections.Generic.List<IOperand>{new Register(null,"X8"),new Register(null,"X0")};
        for(var i=0;i<8;i++)ops.Add(new Register(null,"X"+i));
        for(var i=0;i<8;i++)ops.Add(new Register(null,"V"+i));
        var call=new Instruction(0,tail?OpCode.IndirectJump:OpCode.IndirectCall,ops);
        Assert.That(call.MarkArm64IndirectArgumentSnapshot(),Is.True);
        var argument=new LocalVariable("actualValue",new Register(null,"X19",1),type);
        var result=new LocalVariable("result",new Register(null,"X0",2));
        call.SetOperand(0,new MemoryOperand(info));call.SetOperand(1,result);
        call.SetOperand(2,argument);call.SetOperand(3,info);
        method.ControlFlowGraph=tail?new([call]):new([call,new Instruction(1,OpCode.Return,result)]);
        method.Locals=[argument,result];method.ParameterLocals=[];method.AnalysisWarnings=[];
        Assert.That(MethodInfoTailRecovery.Recover(method),Is.True);
        Assert.That(call.Operands[0],Is.SameAs(target));
        Assert.That(call.Operands[2],Is.SameAs(argument));
        Assert.That(((LocalVariable)call.Destination!).Type,Is.SameAs(type));
        Assert.That(argument.Type,Is.SameAs(type));
    }
}
