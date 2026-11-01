using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AssetRipper.Primitives;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayObjectVirtualDispatchTests
{
    [TestCase("valid", true)]
    [TestCase("misaligned", false)]
    [TestCase("unknown-slot", false)]
    [TestCase("pointer", false)]
    [TestCase("wrong-layout", false)]
    public void ArrayToStringUsesOnlyMetadataConfirmedObjectSlot(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;
        var target=owner.Methods.Single(m=>m.Name=="ToString" && m.Parameters.Count==0);
        TypeAnalysisContext array=shape=="pointer"?new PointerTypeAnalysisContext(owner):new SzArrayTypeAnalysisContext(owner);
        var klass=new LocalVariable("klass",new Register(null,"X9"),new RuntimeClassTypeAnalysisContext(array,owner.DeclaringAssembly));
        var receiver=new LocalVariable("array",new Register(null,"X0"),array);
        var result=new LocalVariable("result",new Register(null,"X0"));
        var layout=RuntimeMetadataLayout.For(new UnityVersion(2018,4,28,UnityVersionType.Final,1),8);
        if(shape=="wrong-layout")layout=layout with { VTable=0x138 };
        var offset=layout.VTable+(shape=="unknown-slot"?200:target.Definition!.slot)*16+(shape=="misaligned"?1:0);
        var call=new Instruction(0,OpCode.IndirectCall,new MemoryOperand(klass,addend:offset),result,receiver,
            new MemoryOperand(klass,addend:offset+8));
        var method=new InjectedMethodAnalysisContext(owner,"Caller",target.ReturnType,MethodAttributes.Public|MethodAttributes.Static,[]);
        method.ControlFlowGraph=new([call,new Instruction(1,OpCode.Return,result)]);
        method.Locals=new List<LocalVariable>{klass,receiver,result};method.ParameterLocals=[];method.AnalysisWarnings=[];
        Assert.That(MetadataResolver.ResolveVirtualCalls(method,layout),Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(call.Operands[0],Is.SameAs(target));
            Assert.That(call.NativeVirtualDispatch,Is.True);
            Assert.That(call.Destination,Is.SameAs(result));
        }
        else Assert.That(call.OpCode,Is.EqualTo(OpCode.IndirectCall));
    }
}
