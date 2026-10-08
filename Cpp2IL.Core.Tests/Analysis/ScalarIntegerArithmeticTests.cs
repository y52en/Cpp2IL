using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ScalarIntegerArithmeticTests
{
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
