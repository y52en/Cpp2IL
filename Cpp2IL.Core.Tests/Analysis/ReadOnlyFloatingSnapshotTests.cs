using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ReadOnlyFloatingSnapshotTests
{
    [TestCase("valid",true)]
    [TestCase("double",true)]
    [TestCase("two-fp-uses",true)]
    [TestCase("already-typed",true)]
    [TestCase("mixed-width",false)]
    [TestCase("integer-use",false)]
    [TestCase("unknown-fp-width",false)]
    [TestCase("address-escape",false)]
    [TestCase("memory-use",false)]
    [TestCase("field-destination",false)]
    [TestCase("array-destination",false)]
    [TestCase("call",false)]
    [TestCase("incoming",false)]
    [TestCase("multiple-definitions",false)]
    [TestCase("unreadable",false)]
    [TestCase("conflicting-type",false)]
    [TestCase("use-before-load",false)]
    [TestCase("indexed-source",false)]
    [TestCase("no-use",false)]
    public void OnlyImmutableReadonlyLoadsWithAllNativeFloatingUsesAreTyped(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Fixture",t.SystemVoidType,MethodAttributes.Static,[]);
        var local=new LocalVariable("literal",new Register(null,"V0"));
        var output=new LocalVariable("result",new Register(null,"V1"),t.SystemSingleType);
        var load=new Instruction(0,OpCode.Move,local,new MemoryOperand(null,addend:0x1234))
            {NativeReadSize=shape=="double"?8:4};
        var use=new Instruction(1,OpCode.Multiply,output,new FloatLiteral(2f),local)
            {NativeFloatingPointSize=shape=="double"?8:4};
        var list=new System.Collections.Generic.List<Instruction>{load,use,new(2,OpCode.Return)};
        if(shape=="already-typed")local.Type=t.SystemSingleType;
        if(shape=="conflicting-type")local.Type=t.SystemObjectType;
        if(shape=="incoming")method.ParameterLocals.Add(local);
        if(shape=="multiple-definitions")list.Insert(1,new(3,OpCode.Move,local,new Immediate(0)));
        if(shape=="two-fp-uses")list.Insert(2,new(3,OpCode.Negate,output,local){NativeFloatingPointSize=4});
        if(shape=="mixed-width")list.Insert(2,new(3,OpCode.Negate,output,local){NativeFloatingPointSize=8});
        if(shape=="integer-use")use.NativeFloatingPointSize=0;
        if(shape=="unknown-fp-width")use.NativeFloatingPointSize=16;
        if(shape=="address-escape")list.Insert(2,new(3,OpCode.CallVoid,new Immediate(123),new AddressOf(local)));
        if(shape=="memory-use")list.Insert(2,new(3,OpCode.Move,new MemoryOperand(local),new Immediate(0)));
        if(shape=="field-destination")list.Insert(2,new(3,OpCode.Move,
            new FieldReference(t.SystemInt32Type.Fields.First(f=>!f.IsStatic),local,0),new Immediate(0)));
        if(shape=="array-destination")list.Insert(2,new(3,OpCode.Move,
            new ArrayAccess(local,new Immediate(0)),new Immediate(0)));
        if(shape=="call")list.Insert(2,new(3,OpCode.CallVoid,new Immediate(123),local));
        if(shape=="use-before-load"){list.Remove(use);list.Insert(0,use);}
        if(shape=="indexed-source")load.SetOperand(1,new MemoryOperand(local,addend:0x1234));
        if(shape=="no-use")list.Remove(use);
        method.ControlFlowGraph=new(list);
        var before=method.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();var beforeType=local.Type;
        var reads=0;
        bool Read(ulong address,int width,out ulong bits)
        {reads++;Assert.That(address,Is.EqualTo(0x1234));bits=width==4?0x3c23d70aul:0x3f847ae147ae147bul;return shape!="unreadable";}
        Assert.That(ReadOnlyScalarRecovery.RecoverFloatingSnapshots(method,Read)>0,Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(local.Type!.FullName,Is.EqualTo(shape=="double"?"System.Double":"System.Single"));
            Assert.That(load.Operands[1],shape=="double"?Is.TypeOf<DoubleLiteral>():Is.TypeOf<FloatLiteral>());
            Assert.That(reads,Is.EqualTo(1));
        }
        else
        {
            Assert.That(local.Type,Is.SameAs(beforeType));
            Assert.That(method.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
        }
    }
}
