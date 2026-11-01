using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedGenericFieldGetterTests
{
    [TestCase("definition",true)] [TestCase("open-self",true)] [TestCase("closed",false)] [TestCase("other-owner",false)]
    public void ReceiverIsTheSameDefinitionWithExactlyItsOwnFormalParameters(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Receiver",t.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner);
        owner.GenericParameters.Add(parameter);
        TypeAnalysisContext candidate=shape switch {
            "definition"=>owner,"open-self"=>new GenericInstanceTypeAnalysisContext(owner,[parameter]),
            "closed"=>new GenericInstanceTypeAnalysisContext(owner,[t.SystemStringType]),_=>t.SystemObjectType};
        Assert.That(SharedGenericFieldGetterRecovery.IsOpenSelf(candidate,owner),Is.EqualTo(expected));
    }
    [TestCase("pure",true)] [TestCase("missing-variant-proof",false)]
    [TestCase("different-field",false)] [TestCase("missing-lane",false)]
    [TestCase("wrong-register",false)] [TestCase("wrong-width",false)]
    [TestCase("wrong-bank",false)] [TestCase("duplicate-lane",false)]
    [TestCase("unattested-field",false)] [TestCase("no-variants",false)]
    public void EveryConcreteScalarReferenceAndAggregateMustReadTheSameGenericField(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","Pair",t.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner);
        owner.GenericParameters.Add(parameter);
        var first=owner.InjectFieldContext("First",parameter,FieldAttributes.Public);
        var second=owner.InjectFieldContext("Second",parameter,FieldAttributes.Public);
        var before=owner.Fields.Select(f=>f.Offset).ToArray();
        var method=new InjectedMethodAnalysisContext(owner,"Get",parameter,MethodAttributes.Public,[]);
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="UnityEngine.Vector2");
        var integer=new ConcreteGenericMethodAnalysisContext(method,[t.SystemInt32Type],[]);
        var floating=new ConcreteGenericMethodAnalysisContext(method,[vector],[]);
        var reference=new ConcreteGenericMethodAnalysisContext(method,[t.SystemStringType],[]);
        var variants=new[]{integer,floating,reference};
        IReadOnlyList<NativeFieldLoadProofs.Read>? Reads(ConcreteGenericMethodAnalysisContext variant)
        {
            if(ReferenceEquals(variant,integer))return [new("gpr",0,4,20,0)];
            if(ReferenceEquals(variant,reference))return [new("gpr",0,8,24,0)];
            if(shape=="missing-variant-proof")return null;
            var result=new List<NativeFieldLoadProofs.Read>{new("fp",0,4,24,0),new("fp",1,4,28,0)};
            if(shape=="different-field")result=result.Select(r=>r with {Offset=r.Offset-8}).ToList();
            if(shape=="missing-lane")result.RemoveAt(1);
            if(shape=="wrong-register")result[1]=result[1] with {Register=2};
            if(shape=="wrong-width")result[1]=result[1] with {Width=8};
            if(shape=="wrong-bank")result[1]=result[1] with {Kind="gpr"};
            if(shape=="duplicate-lane")result[1]=result[0];
            return result;
        }
        var proof=SharedGenericFieldGetterRecovery.Prove(owner,parameter,shape=="no-variants"?[]:variants,Reads,_=>shape!="unattested-field");
        Assert.That(proof,Is.SameAs(expected?second:null));
        Assert.That(owner.Fields.Select(f=>f.Offset),Is.EqualTo(before),"Never write concrete offsets into open T metadata");
    }

    [TestCase("0004432DC0035FD6",2)] // LDP S0,S1,[X0,#24];RET
    [TestCase("0004416DC0035FD6",2)] // LDP D0,D1,[X0,#16];RET
    [TestCase("000C40F9C0035FD6",1)]
    [TestCase("001840B9C0035FD6",1)]
    public void CompleteLoadLeavesRetainNativeBankWidthAndAddress(string hex,int count)
    {
        var result=NativeFieldLoadProofs.Decode(Convert.FromHexString(hex));
        Assert.That(result,Is.Not.Null);Assert.That(result!.Length,Is.EqualTo(count));
        Assert.That(result.Select(r=>r.Register),Is.EqualTo(Enumerable.Range(0,count)));
        Assert.That(result.All(r=>r.Offset>=16),Is.True);
    }

    [TestCase("0004432D")] [TestCase("0004432DC0035FD61F2003D5")]
    [TestCase("0004432D00000014")] [TestCase("2004432DC0035FD6")]
    [TestCase("0004002DC0035FD6")] [TestCase("0004C32CC0035FD6")]
    [TestCase("0004C32DC0035FD6")] [TestCase("000840B9C0035FD6")]
    [TestCase("000C40F9011040F9C0035FD6")]
    public void PartialEffectsStoresWritebackHeadersOrClobberedReceiverAreNotProven(string hex)
        =>Assert.That(NativeFieldLoadProofs.Decode(Convert.FromHexString(hex)),Is.Null);
}
