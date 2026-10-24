using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InlineBoxedHfaTests
{
    [TestCase("valid",true)]
    [TestCase("image",false)]
    [TestCase("metadata",false)]
    [TestCase("schema",false)]
    [TestCase("not-diagnostic",false)]
    [TestCase("adoption",false)]
    public void ProofsCannotCrossOriginalImageMetadataOrCertificationBoundaries(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var image=Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(app.Binary.GetRawBinaryContent()));
        var metadata=Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(((System.IO.MemoryStream)app.Metadata.BaseStream).ToArray()));
        var value=new {schema=shape=="schema"?"wrong":"inline-adjustor-native-counterparts-v1",
            diagnostic_only=shape!="not-diagnostic",adoption_allowed=shape=="adoption",
            loaded_image_sha256=shape=="image"?new string('0',64):image,
            metadata_sha256=shape=="metadata"?new string('0',64):metadata};
        using var document=System.Text.Json.JsonDocument.Parse(System.Text.Json.JsonSerializer.Serialize(value));
        Assert.That(InlineBoxedHfaRecovery.IdentityMatches(app,document.RootElement),Is.EqualTo(expected));
    }

    [TestCase("store",true)]
    [TestCase("load",true)]
    [TestCase("pair",true)]
    [TestCase("partial",false)]
    [TestCase("unknown-width",false)]
    [TestCase("indexed",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("receiver-escape",false)]
    [TestCase("wrong-peer",false)]
    [TestCase("missing-access",false)]
    [TestCase("extra-access",false)]
    [TestCase("incomplete-native",false)]
    [TestCase("native-branch",false)]
    [TestCase("static",false)]
    public void RequiresCompleteNativeCounterpartAndEveryCanonicalReceiverAccess(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var type=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var method=new InjectedMethodAnalysisContext(type,"Test",shape=="load"?app.SystemTypes.SystemSingleType:app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|(shape=="static"?MethodAttributes.Static:0),[]);
        var self=new Register(null,"X0");method.ParameterOperands=[self];
        var memory=new MemoryOperand(self,addend:16);var value=new Register(null,"V0");
        var move=new Instruction(0,OpCode.Move,memory,value){NativeWriteSize=4};
        var original=Convert.FromHexString("001000bdc0035fd6");
        var counterpart=Convert.FromHexString("000000bdc0035fd6");
        if(shape=="load")
        {move=new(0,OpCode.Move,value,memory){NativeReadSize=4};original=Convert.FromHexString("001040bdc0035fd6");counterpart=Convert.FromHexString("000040bdc0035fd6");}
        var list=new System.Collections.Generic.List<Instruction>{move};
        if(shape=="pair")
        {original=Convert.FromHexString("0004022dc0035fd6");counterpart=Convert.FromHexString("0004002dc0035fd6");
            list.Add(new(1,OpCode.Move,new MemoryOperand(self,addend:20),new Register(null,"V1")){NativeWriteSize=4});}
        if(shape=="partial")move.NativeWriteSize=2;
        if(shape=="unknown-width")move.NativeWriteSize=0;
        if(shape=="indexed")move.SetOperand(0,new MemoryOperand(self,new Register(null,"X1"),16,1));
        if(shape=="wrong-offset")move.SetOperand(0,new MemoryOperand(self,addend:20));
        if(shape=="receiver-escape")list.Add(new(2,OpCode.Move,new Register(null,"X2"),self));
        if(shape=="wrong-peer")counterpart[0]=1;
        if(shape=="missing-access")list.Clear();
        if(shape=="extra-access")list.Add(new(2,OpCode.Move,new MemoryOperand(self,addend:20),new Register(null,"V1")){NativeWriteSize=4});
        if(shape=="incomplete-native")original=original[..4];
        if(shape=="native-branch")original=Convert.FromHexString("00000014c0035fd6");
        list.Add(shape=="load"?new(3,OpCode.Return,value):new(3,OpCode.Return));method.ControlFlowGraph=new(list);
        var before=method.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(InlineBoxedHfaRecovery.Recover(method,original,counterpart)>0,Is.EqualTo(expected));
        if(!expected)Assert.That(method.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));
        else Assert.That(((MemoryOperand)move.Operands[shape=="load"?1:0]).Addend,Is.Zero);
    }
}
