using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class RawHiddenMethodInfoRecoveryTests
{
    private static Register R(string name)=>new(null,name);
    private static MemoryOperand Cell(long address)=>new(addend:address);

    [TestCase("direct",true)]
    [TestCase("got",true)]
    [TestCase("copy",true)]
    [TestCase("saved-pointer",true)]
    [TestCase("unapproved-got",false)]
    [TestCase("pointer-overwritten",false)]
    [TestCase("metadata-overwritten",false)]
    [TestCase("volatile-call",false)]
    [TestCase("offset-dereference",false)]
    [TestCase("literal",false)]
    public void OnlyActualReachingMetadataLoadsAreResolved(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var caller=app.SystemTypes.SystemObjectType.Methods[0];
        var target=app.SystemTypes.SystemObjectType.Methods[1];var block=new Block();
        if(shape=="direct")block.Instructions.Add(new(0,OpCode.Move,R("X1"),Cell(0x1234)));
        else if(shape=="literal")block.Instructions.Add(new(0,OpCode.Move,R("X1"),new Immediate(0x1234)));
        else
        {
            var pointer=shape=="saved-pointer"?"X20":"X8";
            block.Instructions.Add(new(0,OpCode.Move,R(pointer),Cell(0x2000)));
            if(shape=="saved-pointer")block.Instructions.Add(new(1,OpCode.CallVoid,new Immediate(0x4000)));
            if(shape=="pointer-overwritten")block.Instructions.Add(new(2,OpCode.Move,R(pointer),new Immediate(0)));
            block.Instructions.Add(new(3,OpCode.Move,R("X1"),new MemoryOperand(R(pointer),addend:shape=="offset-dereference"?8:0)));
            if(shape=="copy")
            {
                block.Instructions.Add(new(4,OpCode.Move,R("X19"),R("X1")));
                block.Instructions.Add(new(5,OpCode.Move,R("X1"),new Immediate(0)));
                block.Instructions.Add(new(6,OpCode.Move,R("X1"),R("X19")));
            }
            if(shape=="metadata-overwritten")block.Instructions.Add(new(7,OpCode.Move,R("X1"),new Immediate(0)));
            if(shape=="volatile-call")block.Instructions.Add(new(8,OpCode.CallVoid,new Immediate(0x4000)));
        }
        var actual=RawHiddenMethodInfoRecovery.Resolve(caller,block,block.Instructions.Count,R("X1"),
            address=>address==0x1234?target:null,
            slot=>slot==0x2000&&shape!="unapproved-got"?0x1234UL:null);
        if(expected)Assert.That(actual,Is.SameAs(target));else Assert.That(actual,Is.Null);
    }

    [TestCase(false,true)]
    [TestCase(true,false)]
    public void UniquePredecessorWorksButUnknownMergeDoesNot(bool merge,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var method=app.SystemTypes.SystemObjectType.Methods[0];
        var predecessor=new Block();predecessor.Instructions.Add(new(0,OpCode.Move,R("X1"),Cell(0x1234)));
        var block=new Block();block.Predecessors.Add(predecessor);
        if(merge)block.Predecessors.Add(new Block());
        var actual=RawHiddenMethodInfoRecovery.Resolve(method,block,0,R("X1"),_=>method,_=>null);
        if(expected)Assert.That(actual,Is.SameAs(method));else Assert.That(actual,Is.Null);
    }

    private static (ApplicationAnalysisContext App,MethodAnalysisContext Caller,ConcreteGenericMethodAnalysisContext Target) Fixture()
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var target=app.ConcreteGenericMethodsByRef.Values.First(m=>!m.IsStatic&&m.Parameters.Count==0
            &&m.UnderlyingPointer!=0&&m.DeclaringType?.IsValueType==false&&!m.ReturnType.HasAnyGenericParameters()
            &&new Arm64CallingConventionResolver().ReturnsViaHiddenBuffer(m));
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"RawBufferCaller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        return(app,caller,target);
    }

    [TestCase("exact",true)]
    [TestCase("different-entry",false)]
    [TestCase("own-metadata",false)]
    [TestCase("foreign-definition",false)]
    [TestCase("argument-conflict",false)]
    [TestCase("static-conflict",false)]
    public void ClosedMetadataMustMatchTheActualEntryDefinitionAndArgumentSlot(string shape,bool expected)
    {
        var(app,caller,target)=Fixture();var block=new Block();
        block.Instructions.Add(new(0,OpCode.Move,R("X1"),Cell(0x1234)));
        var entry=target.UnderlyingPointer+(shape=="different-entry"?4UL:0UL);
        MethodAnalysisContext[] candidates=[target.BaseMethodContext,target];
        if(shape=="foreign-definition")candidates=[app.SystemTypes.SystemObjectType.Methods[0]];
        if(shape=="argument-conflict")candidates=[target,app.SystemTypes.SystemObjectType.Methods.First(m=>m.Parameters.Count>0)];
        if(shape=="static-conflict")candidates=[target,new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"StaticAlias",target.ReturnType,
            MethodAttributes.Public|MethodAttributes.Static,[])];
        var actual=HiddenStructReturnRecovery.ExactZeroArgumentTarget(caller,block,1,entry,candidates,
            address=>shape=="own-metadata"?caller:target,_=>null);
        if(expected)Assert.That(actual,Is.SameAs(target));else Assert.That(actual,Is.Null);
    }
}
