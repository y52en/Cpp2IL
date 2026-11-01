using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypedFloatLocalLiteralTests
{
    [TestCase(false,0L)]
    [TestCase(false,1065353216L)]
    [TestCase(false,-2147483648L)]
    [TestCase(true,0L)]
    [TestCase(true,4607182418800017408L)]
    [TestCase(true,long.MinValue)]
    public void TypedLocalCopyRetainsLiteralBitsIncludingPhiZeroAndNegativeZero(bool wide,long bits)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=wide?app.SystemTypes.SystemDoubleType:app.SystemTypes.SystemSingleType;
        var destination=new LocalVariable("merged",new Register(null,"V0"),type);
        var move=new Instruction(0,OpCode.Move,destination,new Immediate(bits));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([move,new(1,OpCode.Return)]);
        FloatLiteralRecovery.Run(method);
        if(wide) Assert.That(BitConverter.DoubleToInt64Bits(((DoubleLiteral)move.Operands[1]).Value),Is.EqualTo(bits));
        else Assert.That(BitConverter.SingleToInt32Bits(((FloatLiteral)move.Operands[1]).Value),Is.EqualTo(unchecked((int)bits)));
    }

    [TestCase("integer")]
    [TestCase("unknown")]
    [TestCase("subnormal")]
    [TestCase("numeric-conversion")]
    public void UnprovenOrNumericIntegerValuesAreNotBitReinterpreted(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();var types=app.SystemTypes;
        var destination=new LocalVariable("value",new Register(null,"V0"),shape=="unknown"?null:shape=="integer"?types.SystemInt32Type:types.SystemSingleType);
        var original=new Immediate(shape=="subnormal"?1:0);
        var instruction=shape=="numeric-conversion"
            ?new Instruction(0,OpCode.NumericConvert,destination,types.SystemSingleType,types.SystemInt32Type,original)
            :new Instruction(0,OpCode.Move,destination,original);
        var method=new InjectedMethodAnalysisContext(types.SystemObjectType,"Caller",types.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([instruction,new(1,OpCode.Return)]);
        FloatLiteralRecovery.Run(method);
        Assert.That(instruction.Operands[shape=="numeric-conversion"?3:1],Is.EqualTo(original));
    }
}
