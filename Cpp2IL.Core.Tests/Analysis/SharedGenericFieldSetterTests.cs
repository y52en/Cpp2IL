using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedGenericFieldSetterTests
{
    [TestCase("pure",true)] [TestCase("missing-variant-proof",false)]
    [TestCase("different-field",false)] [TestCase("missing-lane",false)]
    [TestCase("wrong-register",false)] [TestCase("wrong-width",false)]
    [TestCase("wrong-bank",false)] [TestCase("duplicate-lane",false)]
    [TestCase("unattested-field",false)] [TestCase("no-variants",false)]
    [TestCase("readonly-field",false)] [TestCase("extra-argument",false)]
    [TestCase("static",false)] [TestCase("nonvoid",false)]
    public void EveryClosedScalarReferenceAndHfaMustStoreTheSameDeclaredArgument(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","SetterPair",t.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,Il2CppTypeEnum.IL2CPP_TYPE_VAR,GenericParameterAttributes.None,owner);
        owner.GenericParameters.Add(parameter);
        owner.InjectFieldContext("First",parameter,FieldAttributes.Public);
        var second=owner.InjectFieldContext("Second",parameter,shape=="readonly-field"?FieldAttributes.Public|FieldAttributes.InitOnly:FieldAttributes.Public);
        var before=owner.Fields.Select(f=>f.Offset).ToArray();
        var method=new InjectedMethodAnalysisContext(owner,"Set",shape=="nonvoid"?parameter:t.SystemVoidType,
            shape=="static"?MethodAttributes.Public|MethodAttributes.Static:MethodAttributes.Public,
            shape=="extra-argument"?[parameter,t.SystemInt32Type]:[parameter]);
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="UnityEngine.Vector2");
        var integer=new ConcreteGenericMethodAnalysisContext(method,[t.SystemInt32Type],[]);
        var floating=new ConcreteGenericMethodAnalysisContext(method,[vector],[]);
        var reference=new ConcreteGenericMethodAnalysisContext(method,[t.SystemStringType],[]);
        IReadOnlyList<NativeFieldLoadProofs.Read>? Stores(ConcreteGenericMethodAnalysisContext variant)
        {
            if(ReferenceEquals(variant,integer))return [new("gpr",1,4,20,0)];
            if(ReferenceEquals(variant,reference))return [new("gpr",1,8,24,0)];
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
        var proof=SharedGenericFieldSetterRecovery.Prove(owner,parameter,shape=="no-variants"?[]:[integer,floating,reference],
            Stores,_=>shape!="unattested-field");
        Assert.That(proof,Is.SameAs(expected?second:null));
        Assert.That(owner.Fields.Select(f=>f.Offset),Is.EqualTo(before),"Never mutate generic definition field offsets");
    }

    [TestCase("01400039C0035FD6",1)] [TestCase("01200079C0035FD6",1)]
    [TestCase("011000B9C0035FD6",1)] [TestCase("010800F9C0035FD6",1)]
    [TestCase("001000BDC0035FD6",1)] [TestCase("000800FDC0035FD6",1)]
    [TestCase("0004022DC0035FD6",2)] [TestCase("010801A9C0035FD6",2)]
    public void CompleteStoreLeavesDecodeAllArgumentBanks(string hex,int count)
    {
        var effects=NativeFieldStoreProofs.Decode(Convert.FromHexString(hex));
        Assert.That(effects,Is.Not.Null);Assert.That(effects!.Length,Is.EqualTo(count));
        Assert.That(effects.All(s=>s.Offset>=16),Is.True);
        Assert.That(effects.Select(s=>s.Register),Is.EqualTo(Enumerable.Range(effects[0].Kind=="gpr"?1:0,count)));
    }

    [TestCase("001040BDC0035FD6")] [TestCase("201000BDC0035FD6")]
    [TestCase("000800F9C0035FD6")] [TestCase("1F0800F9C0035FD6")]
    [TestCase("041000BDC0035FD6")] [TestCase("010000B9C0035FD6")]
    [TestCase("010881A9C0035FD6")] [TestCase("001000BD011000BDC0035FD6")]
    [TestCase("001000BD001400BDC0035FD6")] [TestCase("010800F9001800BDC0035FD6")]
    [TestCase("001000BD00000094C0035FD6")] [TestCase("001000BD00000000")]
    [TestCase("001000BD")]
    public void LoadsOtherArgumentsHeadersWritebackOverlapOrExtraEffectsAreRejected(string hex)
        =>Assert.That(NativeFieldStoreProofs.Decode(Convert.FromHexString(hex)),Is.Null);
}
