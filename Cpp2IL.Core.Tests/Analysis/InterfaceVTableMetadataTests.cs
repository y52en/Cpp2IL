using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceVTableMetadataTests
{
    [TestCase("valid",true)]
    [TestCase("function-half",false)]
    [TestCase("misaligned",false)]
    [TestCase("unknown-slot",false)]
    [TestCase("partial-info",false)]
    [TestCase("partial-header",false)]
    [TestCase("header-offset",false)]
    [TestCase("indexed",false)]
    [TestCase("wrong-type",false)]
    [TestCase("unknown-type",false)]
    [TestCase("duplicate-info",false)]
    [TestCase("duplicate-header",false)]
    [TestCase("late-header",false)]
    [TestCase("wrong-layout",false)]
    public void RequiresExactTypedNativeMethodInfoHalf(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.First(m=>m.IsVirtual && m.Definition is {slot:<ushort.MaxValue}
            && m.GenericParameters.Count==0 && m.Parameters.Count==0);
        var method=new InjectedMethodAnalysisContext(owner,"MetadataLeaf",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var receiver=new LocalVariable("receiver",new(null,"X0"),shape=="wrong-type" ? app.SystemTypes.SystemStringType : owner);
        if(shape=="unknown-type")receiver.Type=null;
        var klass=new LocalVariable("klass",new(null,"X8"),new RuntimeClassTypeAnalysisContext(owner,owner.DeclaringAssembly));
        var info=new LocalVariable("info",new(null,"X1"));
        var layout=RuntimeMetadataLayout.For(new UnityVersion(2018,4,28,UnityVersionType.Final,1),8);
        var offset=layout.VTable+target.Definition!.slot*16+8;
        if(shape=="function-half")offset-=8;
        if(shape=="misaligned")offset++;
        if(shape=="unknown-slot")offset+=65536;
        var header=new Instruction(0,OpCode.Move,klass,new MemoryOperand(receiver,addend:shape=="header-offset"?8:0))
            {NativeReadSize=shape=="partial-header"?4:8};
        var load=new Instruction(1,OpCode.Move,info,new MemoryOperand(klass,
            indexRegister:shape=="indexed"?receiver:null,addend:offset)) {NativeReadSize=shape=="partial-info"?4:8};
        var instructions=new List<Instruction>{header,load,new(2,OpCode.Return)};
        if(shape=="duplicate-info")instructions.Insert(2,new(3,OpCode.Move,info,new Immediate(0)));
        if(shape=="duplicate-header")instructions.Insert(2,new(3,OpCode.Move,klass,new Immediate(0)));
        if(shape=="late-header"){instructions.Remove(header);instructions.Insert(1,header);}
        method.ControlFlowGraph=new(instructions);
        if(shape=="wrong-layout")layout=layout with {VTable=0x138};
        var definitions=new Dictionary<LocalVariable,Instruction>{{klass,header},{info,load}};
        Assert.That(InterfaceDispatchRecovery.IsKnownVTableMethodInfo(method,info,definitions,layout),Is.EqualTo(expected));
    }
}
