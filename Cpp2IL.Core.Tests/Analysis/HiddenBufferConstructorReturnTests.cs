using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class HiddenBufferConstructorReturnTests
{
    [TestCase("valid",true)]
    [TestCase("missing-field",false)]
    [TestCase("duplicate-field",false)]
    [TestCase("partial-store",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("not-incoming-buffer",false)]
    [TestCase("wrong-buffer-register",false)]
    [TestCase("different-return",false)]
    [TestCase("callback",false)]
    [TestCase("nonzero",false)]
    [TestCase("unproven-buffer",false)]
    [TestCase("equivalent-owner",true)]
    [TestCase("wrong-owner",false)]
    public void OnlyFullyInitializedIncomingStorageIsReturnedAfterTheVoidConstructor(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var definition=app.Assemblies.SelectMany(a=>a.Types)
            .Single(t=>t.FullName=="System.Collections.Generic.List`1+Enumerator");
        var type=new GenericInstanceTypeAnalysisContext(definition,[app.SystemTypes.SystemObjectType]);
        var layout=ClosedGenericValueLayout.Fields(type,8)!;
        var buffer=new LocalVariable("buffer",new Register(null,shape=="wrong-buffer-register"?"X9":"X8",
            shape=="not-incoming-buffer"?1:-1),type){IsReturnBuffer=shape!="unproven-buffer"};
        var discarded=new LocalVariable("undefinedX0",new Register(null,"X0",1),type){IsReturn=true};
        var list=new LocalVariable("list",new Register(null,"X0"),layout[0].Field.FieldType);
        var ctorOwner=shape is "equivalent-owner" or "wrong-owner"
            ?new GenericInstanceTypeAnalysisContext(definition,[shape=="wrong-owner"?app.SystemTypes.SystemStringType:app.SystemTypes.SystemObjectType])
            :type;
        var ctor=new InjectedMethodAnalysisContext(ctorOwner,".ctor",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public,[list.Type!]);
        var call=new Instruction(10,OpCode.Call,ctor,discarded,buffer,list);
        var ret=new Instruction(11,OpCode.Return,shape=="different-return"?list:discarded);
        var writes=layout.Select((f,i)=>new Instruction(i,OpCode.Move,new FieldReference(f.Field,buffer,(int)f.Offset),
            new Immediate(shape=="nonzero"?1:0)){NativeWriteSize=(int)f.Size}).ToList();
        if(shape=="missing-field")writes.RemoveAt(0);
        if(shape=="duplicate-field")writes[1].SetOperand(0,writes[0].Operands[0]);
        if(shape=="partial-store")writes[0].NativeWriteSize=4;
        if(shape=="wrong-offset")((FieldReference)writes[0].Operands[0]).Offset=4;
        if(shape=="callback")writes.Add(new(9,OpCode.CallVoid,new StringLiteral("callback")));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",type,
            MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new ISILControlFlowGraph([..writes,call,ret]),Locals=[buffer,discarded,list]};
        method.ControlFlowGraph.MergeCallBlocks(); // same late graph shape as production
        var before=string.Join("\n",method.ControlFlowGraph.Instructions.Select(i=>i.ToString()));
        Assert.That(HiddenBufferConstructorReturnRecovery.Recover(method),Is.EqualTo(expected));
        if(expected)
        {
            Assert.That(call.OpCode,Is.EqualTo(OpCode.CallVoid));
            Assert.That(((AddressOf)call.Operands[1]).Target,Is.SameAs(buffer));
            Assert.That(ret.Operands[0],Is.SameAs(buffer));
            Assert.That(HiddenBufferConstructorReturnRecovery.Recover(method),Is.False);
        }
        else Assert.That(string.Join("\n",method.ControlFlowGraph.Instructions.Select(i=>i.ToString())),Is.EqualTo(before));
    }
}
