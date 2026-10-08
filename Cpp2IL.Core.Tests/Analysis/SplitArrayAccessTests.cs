using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SplitArrayAccessTests
{
    [TestCase(false,8,32,3,true)]
    [TestCase(true,8,32,3,true)]
    [TestCase(false,4,32,3,false)] // Partial reference read.
    [TestCase(false,8,24,3,false)] // Header, not elements.
    [TestCase(false,8,32,2,false)] // Wrong element stride.
    [TestCase(false,0,32,3,false)] // Unknown width cannot be treated as load.
    public void SplitNativeAddressRequiresExactWidthAndStride(bool store,int width,int header,int shift,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var type=app.SystemTypes.SystemObjectType;
        var array=new LocalVariable("array",new Register(null,"X19"),new SzArrayTypeAnalysisContext(type));
        var index=new LocalVariable("index",new Register(null,"X20"),app.SystemTypes.SystemInt32Type);
        var scaled=new LocalVariable("scaled",new Register(null,"TMP"));
        var address=new LocalVariable("address",new Register(null,"X8"));
        var value=new LocalVariable("value",new Register(null,"X0"),type);
        var memory=new MemoryOperand(address,addend:header);
        var access=store ? new Instruction(2,OpCode.Move,memory,value){NativeWriteSize=width}
            : new Instruction(2,OpCode.Move,value,memory){NativeReadSize=width};
        var method=new InjectedMethodAnalysisContext(type,"Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([
            new(0,OpCode.ShiftLeft,scaled,index,new Immediate(shift)),
            new(1,OpCode.Add,address,array,scaled),access,new(3,OpCode.Return)]);
        Assert.That(ArrayRecovery.RecoverSplitAccesses(method),Is.EqualTo(expected));
        var result=access.Operands[store?0:1] as ArrayAccess;
        Assert.That(result!=null,Is.EqualTo(expected));
        if(result!=null) { Assert.That(result.Array,Is.SameAs(array));Assert.That(result.Index,Is.SameAs(index)); }
    }
}
