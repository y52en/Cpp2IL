using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LateSplitArrayLoadTests
{
    [TestCase("valid",true)]
    [TestCase("unknown-index",true)]
    [TestCase("wide-read",false)]
    [TestCase("unknown-width",false)]
    [TestCase("wrong-scale",false)]
    [TestCase("header",false)]
    [TestCase("offset",false)]
    [TestCase("array-reassigned",false)]
    [TestCase("address-reassigned",false)]
    [TestCase("unanchored-array",false)]
    [TestCase("definition-after-use",false)]
    [TestCase("reference-index",false)]
    [TestCase("untyped-array",false)]
    [TestCase("store",false)]
    [TestCase("implicit-address-clobber",false)]
    [TestCase("implicit-array-clobber",false)]
    [TestCase("other-version-clobber",true)]
    public void LateLoadsRequireStableArrayAndAddressButKeepTheCurrentIndex(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var array=new LocalVariable("array",new(null,"X19"),shape=="untyped-array"?null:new SzArrayTypeAnalysisContext(t.SystemSingleType));
        var index=new LocalVariable("index",new(null,"X21"),shape=="unknown-index"?null:shape=="reference-index"?t.SystemStringType:t.SystemInt64Type);
        var address=new LocalVariable("address",new(null,"X22"));
        var value=new LocalVariable("value",new(null,"V0"),t.SystemSingleType);
        var definition=new Instruction(0,OpCode.Add,address,array,new Immediate(shape=="header"?24:32));
        var memory=new MemoryOperand(address,index,addend:shape=="offset"?4:0,scale:shape=="wrong-scale"?8:4);
        var read=shape=="store"?new Instruction(1,OpCode.Move,memory,value){NativeWriteSize=4}
            :new Instruction(1,OpCode.Move,value,memory){NativeReadSize=shape=="wide-read"?8:shape=="unknown-width"?0:4};
        var update=new Instruction(2,OpCode.Add,index,index,new Immediate(1)){NativeArithmeticSize=8};
        var instructions=new System.Collections.Generic.List<Instruction>{definition,read,update,new(3,OpCode.Return,value)};
        if(shape.Contains("clobber"))instructions.Insert(1,new(4,OpCode.CallVoid,new StringLiteral("callback")){
            ImplicitDefinition=shape=="implicit-address-clobber"?address.Register:
                shape=="implicit-array-clobber"?array.Register:array.Register.Copy(17)});
        if(shape=="array-reassigned")instructions.Insert(1,new(4,OpCode.Move,array,new Immediate(0)));
        if(shape=="address-reassigned")instructions.Insert(1,new(4,OpCode.Add,address,array,new Immediate(64)));
        if(shape=="definition-after-use")instructions=[read,definition,update,instructions[^1]];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",t.SystemSingleType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new(instructions);method.ParameterLocals=[array,index];
        if(shape=="unanchored-array")method.ParameterLocals=[index];
        var before=method.ControlFlowGraph.Instructions.ToArray();var indexType=index.Type;
        Assert.That(ArrayRecovery.RecoverLateSplitLoads(method),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(read.Operands[1],Is.TypeOf<ArrayAccess>());
            Assert.That(((ArrayAccess)read.Operands[1]).Array,Is.SameAs(array));
            Assert.That(((ArrayAccess)read.Operands[1]).Index,Is.SameAs(index));
            Assert.That(method.ControlFlowGraph.Instructions.Contains(update),Is.True);
        }
        else Assert.That(method.ControlFlowGraph.Instructions,Is.EqualTo(before));
        Assert.That(index.Type,Is.SameAs(indexType));
    }
}
