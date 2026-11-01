using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ScalarIntegerArithmeticTests
{
    [TestCase("Byte", false)]
    [TestCase("SByte", false)]
    [TestCase("Int16", false)]
    [TestCase("UInt16", false)]
    [TestCase("Int32", false)]
    [TestCase("UInt32", false)]
    [TestCase("Int64", true)]
    [TestCase("UInt64", true)]
    public void EnumArithmeticUsesMetadataWidthAndKeepsSourceEnum(string underlying, bool wide)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var enumType = new InjectedTypeAnalysisContext(assembly, "Test", "Step", assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public)
            { EnumUnderlyingType = assembly.GetTypeByFullName("System." + underlying)! };
        var left = new LocalVariable("step", new Register(null, "X0"), enumType);
        var result = new LocalVariable("difference", new Register(null, "X1"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Compute", app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new([new(0, OpCode.Subtract, result, left, new Immediate(9)), new(1, OpCode.Return)]);
        method.Locals = [left, result]; method.ParameterLocals = []; method.AnalysisWarnings = [];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type, Is.SameAs(wide ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemInt32Type));
        Assert.That(left.Type, Is.SameAs(enumType));
    }

    [Test]
    public void EnumWithoutUnderlyingMetadataRemainsUnresolved()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var enumType = new InjectedTypeAnalysisContext(assembly, "Test", "Unknown", assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public);
        var left = new LocalVariable("step", new Register(null, "X0"), enumType);
        var result = new LocalVariable("difference", new Register(null, "X1"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Compute", app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        method.ControlFlowGraph = new([new(0, OpCode.Subtract, result, left, new Immediate(9)), new(1, OpCode.Return)]);
        method.Locals = [left, result]; method.ParameterLocals = []; method.AnalysisWarnings = [];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type, Is.Null);
        Assert.That(left.Type, Is.SameAs(enumType));
    }

    [TestCase(OpCode.Add,false)]
    [TestCase(OpCode.Subtract,false)]
    [TestCase(OpCode.Multiply,false)]
    [TestCase(OpCode.Add,true)]
    [TestCase(OpCode.Subtract,true)]
    [TestCase(OpCode.Multiply,true)]
    public void KnownIntegerAndImmediatePropagateThroughActualFixpoint(OpCode opcode,bool wide)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=wide ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemInt32Type;
        var left=new LocalVariable("number",new Register(null,"X0"),type);
        var result=new LocalVariable("result",new Register(null,"X1"));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Compute",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([new(0,opcode,result,left,new Immediate(1)),new(1,OpCode.Return)]);
        method.Locals=[left,result];method.ParameterLocals=[];method.AnalysisWarnings=[];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type,Is.SameAs(type));
    }

    [TestCase("reference")]
    [TestCase("unknown")]
    [TestCase("bool")]
    [TestCase("mixed-width")]
    [TestCase("wide-immediate")]
    public void MixedPointerUnknownAndUnprovenWidthsAreNotGuessed(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var left=new LocalVariable("number",new Register(null,"X0"),app.SystemTypes.SystemInt32Type);
        var rightType=shape switch {
            "reference"=>app.SystemTypes.SystemObjectType,
            "bool"=>app.SystemTypes.SystemBooleanType,
            "mixed-width"=>app.SystemTypes.SystemInt64Type,
            _=>null,
        };
        var right=new LocalVariable("other",new Register(null,"X2"),rightType);
        var result=new LocalVariable("result",new Register(null,"X1"));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Compute",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        IOperand operand=shape=="wide-immediate" ? new Immediate(long.MaxValue) : right;
        method.ControlFlowGraph=new([new(0,OpCode.Add,result,left,operand),new(1,OpCode.Return)]);
        method.Locals=[left,right,result];method.ParameterLocals=[];method.AnalysisWarnings=[];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type,Is.Null);
    }
}
