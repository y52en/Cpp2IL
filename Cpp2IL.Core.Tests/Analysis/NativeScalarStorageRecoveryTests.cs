using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeScalarStorageRecoveryTests
{
    [TestCase("integer64","System.Int64",1)]
    [TestCase("integer32","System.Int32",1)]
    [TestCase("float32","System.Single",1)]
    [TestCase("float64","System.Double",1)]
    [TestCase("copy-cycle","System.Single",2)]
    [TestCase("array-index","System.Int64",1)]
    [TestCase("zero-compare","System.Single",1)]
    [TestCase("high-i4","System.Int32",1)]
    [TestCase("opaque-consumer",null,0)]
    [TestCase("memory-base",null,0)]
    [TestCase("field-receiver",null,0)]
    [TestCase("reference-return",null,0)]
    [TestCase("conflicting-integer-width",null,0)]
    [TestCase("conflicting-float-width",null,0)]
    [TestCase("gp-bitcopy",null,0)]
    [TestCase("unanchored-zero",null,0)]
    [TestCase("parameter-unknown",null,0)]
    [TestCase("reference-call",null,0)]
    [TestCase("integer-divide",null,0)]
    [TestCase("unknown-load",null,0)]
    [TestCase("known-operand-conflict",null,0)]
    public void EveryWriteAndCompleteOperandUseMustAgree(string shape,string? expected,int count)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var floating=shape is "float32" or "float64" or "copy-cycle" or "zero-compare" or "opaque-consumer" or "conflicting-float-width" or "gp-bitcopy";
        var narrow=shape is "integer32" or "high-i4";
        var a=new LocalVariable("a",new(null,floating?"V0":"X21"));
        var b=new LocalVariable("b",new(null,shape=="gp-bitcopy"?"X0":"V1"));
        var initialize=new Instruction(0,OpCode.Move,a,new Immediate(0));
        IOperand step=shape=="float64"?new DoubleLiteral(1):floating?new FloatLiteral(1):new Immediate(shape=="high-i4"?0xffffffff:1);
        var update=new Instruction(1,OpCode.Add,a,a,step){NativeArithmeticSize=floating?0:narrow?4:8,
            NativeFloatingPointSize=floating?shape=="float64"?8:4:0};
        TypeAnalysisContext result=shape=="unanchored-zero"?t.SystemVoidType:shape=="reference-return"?t.SystemObjectType:
            floating?shape=="float64"?t.SystemDoubleType:t.SystemSingleType:narrow?t.SystemInt32Type:t.SystemInt64Type;
        var instructions=new System.Collections.Generic.List<Instruction>{initialize,update,new(2,OpCode.Return,a)};
        if(shape=="copy-cycle"){instructions.Insert(1,new(3,OpCode.Move,b,a));update.SetOperand(1,b);}
        if(shape=="opaque-consumer")instructions.Insert(2,new(3,OpCode.CallVoid,new StringLiteral("opaque"),a));
        if(shape=="memory-base")instructions.Insert(2,new(3,OpCode.Move,new LocalVariable("loaded",new(null,"X2"),t.SystemObjectType),new MemoryOperand(a)){NativeReadSize=8});
        if(shape=="field-receiver")
        {
            var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Holder",t.SystemObjectType,TypeAttributes.Public);
            var field=owner.InjectFieldContext("Value",t.SystemInt32Type,FieldAttributes.Public);field.Offset=16;
            instructions.Insert(2,new(3,OpCode.Move,new LocalVariable("loaded",new(null,"X2"),t.SystemInt32Type),new FieldReference(field,a,16)));
        }
        if(shape=="conflicting-integer-width")instructions.Insert(2,new(3,OpCode.Add,a,a,new Immediate(1)){NativeArithmeticSize=4});
        if(shape=="conflicting-float-width")instructions.Insert(2,new(3,OpCode.Add,a,a,new DoubleLiteral(1)){NativeFloatingPointSize=8});
        if(shape=="gp-bitcopy")instructions.Insert(2,new(3,OpCode.Move,b,a));
        if(shape=="unanchored-zero")instructions=[initialize,new(2,OpCode.Return)];
        if(shape=="integer-divide")instructions.Insert(2,new(3,OpCode.Divide,a,a,new Immediate(2)){NativeArithmeticSize=8});
        if(shape=="unknown-load")initialize.SetOperand(1,new MemoryOperand(addend:0x1000));
        if(shape=="known-operand-conflict")instructions.Insert(2,new(3,OpCode.Add,
            new LocalVariable("known",new(null,"X2"),t.SystemInt64Type),new FloatLiteral(1),a){NativeArithmeticSize=8});
        if(shape=="array-index")
        {
            var array=new LocalVariable("array",new(null,"X19"),new SzArrayTypeAnalysisContext(t.SystemSingleType));
            instructions.Insert(2,new(3,OpCode.Move,new LocalVariable("element",new(null,"V0"),t.SystemSingleType),new ArrayAccess(array,a)));
        }
        if(shape=="zero-compare")instructions.Insert(2,new(3,OpCode.CheckEqual,new LocalVariable("flag",new(null,"flag"),t.SystemBooleanType),a,new Immediate(0)));
        if(shape=="reference-call")
        {
            var target=new InjectedMethodAnalysisContext(t.SystemObjectType,"ReferenceConsumer",t.SystemVoidType,
                MethodAttributes.Public|MethodAttributes.Static,[t.SystemObjectType]);
            instructions.Insert(2,new(3,OpCode.CallVoid,target,a));
        }
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",result,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new(instructions)};
        if(shape=="parameter-unknown")method.ParameterLocals.Add(a);
        Assert.That(NativeScalarStorageRecovery.Recover(method),Is.EqualTo(count));
        Assert.That(a.Type?.FullName,Is.EqualTo(expected));
        if(expected=="System.Single")Assert.That(initialize.Operands[1],Is.TypeOf<FloatLiteral>());
        if(expected=="System.Double")Assert.That(initialize.Operands[1],Is.TypeOf<DoubleLiteral>());
        if(shape=="high-i4")Assert.That(((Immediate)update.Operands[2]).Value,Is.EqualTo(-1));
        if(count==0)Assert.That(initialize.Operands[1],Is.TypeOf<MemoryOperand>().Or.TypeOf<Immediate>());
    }
}
