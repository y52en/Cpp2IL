using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64IndirectArgumentSnapshotTests
{
    private static Instruction Raw(OpCode opcode, out List<IOperand> storage)
    {
        storage = [new Register(null,"X8"), new Register(null,"X0")];
        storage.AddRange(Enumerable.Range(0,8).Select(n=>(IOperand)new Register(null,"X"+n)));
        storage.AddRange(Enumerable.Range(0,8).Select(n=>(IOperand)new Register(null,"V"+n)));
        return new Instruction(0,opcode,storage);
    }

    [TestCase(0xd63f0100u,OpCode.IndirectCall)]
    [TestCase(0xd61f0100u,OpCode.IndirectJump)]
    public void ActualDecodedBrAndBlrCaptureOrderedPhysicalSlots(uint word, OpCode expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(BitConverter.GetBytes(word),0x1000,new(true,true,false)).Single();
        var instructions=new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!
            .SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(),new object[]{native,instructions,new List<ulong>(),method});
        var call=instructions.Single();
        Assert.That(call.OpCode,Is.EqualTo(expected));
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.True);
        Assert.That(call.Operands.Skip(2).Cast<Register>().Select(r=>r.Name),
            Is.EqualTo(Enumerable.Range(0,8).Select(n=>"X"+n).Concat(Enumerable.Range(0,8).Select(n=>"V"+n))));
    }

    [TestCase("short")]
    [TestCase("swapped")]
    [TestCase("already-local")]
    [TestCase("wrong-opcode")]
    public void ProvenanceCannotBeInferredFromCountOrAlreadyFoldedLocals(string shape)
    {
        var call=Raw(shape=="wrong-opcode"?OpCode.Call:OpCode.IndirectCall,out var storage);
        if(shape=="short")storage.RemoveAt(17);
        if(shape=="swapped")(storage[2],storage[3])=(storage[3],storage[2]);
        if(shape=="already-local")storage[2]=new LocalVariable("arg",new Register(null,"X0"));
        Assert.That(call.MarkArm64IndirectArgumentSnapshot(),Is.False);
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.False);
    }

    [TestCase("replace-list")]
    [TestCase("append")]
    [TestCase("remove")]
    [TestCase("opcode")]
    [TestCase("external-alias")]
    public void StructuralMutationInvalidatesEvenWhenShapeIsRestored(string shape)
    {
        var call=Raw(OpCode.IndirectCall,out var storage);
        Assert.That(call.MarkArm64IndirectArgumentSnapshot(),Is.True);
        if(shape=="replace-list")call.SetOperands(call.Operands.ToList());
        if(shape=="append"){call.AddOperands([new Immediate(9)]);call.RemoveOperandAt(18);}
        if(shape=="remove"){call.RemoveOperandAt(17);call.AddOperands([new Register(null,"V7")]);}
        if(shape=="opcode"){call.OpCode=OpCode.Call;call.OpCode=OpCode.IndirectCall;}
        if(shape=="external-alias")(storage[2],storage[3])=(storage[3],storage[2]);
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.False);
    }

    [Test]
    public void PerSlotSsaSubstitutionKeepsValueAndPositionDespiteDifferentRegisterIdentity()
    {
        var call=Raw(OpCode.IndirectCall,out _);call.MarkArm64IndirectArgumentSnapshot();
        var value=new LocalVariable("copied",new Register(null,"X19",3));
        call.SetOperand(3,value);
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.True);
        Assert.That(call.Operands[3],Is.SameAs(value));
        Assert.That(((Register)call.Operands[2]).Name,Is.EqualTo("X0"));
    }

    [Test]
    public void PerSlotRewriteCannotRepairPreviouslyUnobservedExternalMutation()
    {
        var call=Raw(OpCode.IndirectCall,out var storage);call.MarkArm64IndirectArgumentSnapshot();
        var original=storage[2];storage[2]=new Register(null,"X5");
        call.SetOperand(2,original);
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.False);
    }

    [TestCase(false,false)]
    [TestCase(false,true)]
    [TestCase(true,false)]
    [TestCase(true,true)]
    public void CopiedReceiverRequiresNativeProvenanceForCallOrTail(bool marked,bool tail)
        => CheckRecovery(marked,tail,"valid",marked);

    [TestCase("hidden-info")]
    [TestCase("result-register")]
    [TestCase("float-return")]
    public void NativeArgumentProvenanceDoesNotRelaxHiddenInfoOrResultAbi(string shape)
        => CheckRecovery(true,false,shape,false);

    private static void CheckRecovery(bool marked,bool tail,string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var owner=app.SystemTypes.SystemObjectType;
        var type=shape=="float-return"?app.SystemTypes.SystemSingleType:app.SystemTypes.SystemStringType;
        var target=new InjectedMethodAnalysisContext(owner,"Target",type,MethodAttributes.Public,[]);
        var other=new InjectedMethodAnalysisContext(owner,"Other",type,MethodAttributes.Public,[]);
        var info=new RuntimeMethodInfoAnalysisContext(target,owner.DeclaringAssembly);
        var passed=shape=="hidden-info"?new RuntimeMethodInfoAnalysisContext(other,owner.DeclaringAssembly):info;
        var method=new InjectedMethodAnalysisContext(owner,"Caller",type,MethodAttributes.Public|MethodAttributes.Static,[]);
        var call=Raw(tail?OpCode.IndirectJump:OpCode.IndirectCall,out _);
        if(marked)Assert.That(call.MarkArm64IndirectArgumentSnapshot(),Is.True);
        var receiver=new LocalVariable("copiedReceiver",new Register(null,"X19",2),owner);
        var result=new LocalVariable("result",new Register(null,shape=="result-register"?"X3":"X0",3));
        call.SetOperand(0,new MemoryOperand(info));call.SetOperand(1,result);
        call.SetOperand(2,receiver);call.SetOperand(3,passed);
        method.ControlFlowGraph=tail?new([call]):new([call,new Instruction(1,OpCode.Return,result)]);
        method.Locals=[receiver,result];method.ParameterLocals=[];method.AnalysisWarnings=[];
        Assert.That(MethodInfoTailRecovery.Recover(method),Is.EqualTo(expected));
        if(!expected){Assert.That(call.OpCode,Is.EqualTo(tail?OpCode.IndirectJump:OpCode.IndirectCall));return;}
        Assert.That(call.OpCode,Is.EqualTo(OpCode.Call));
        Assert.That(call.Operands[2],Is.SameAs(receiver));
        Assert.That(call.Operands[3],Is.SameAs(info));
        Assert.That(call.HasArm64IndirectArgumentSnapshot,Is.False);
        Assert.That(method.ControlFlowGraph.Instructions.Single(i=>i.OpCode==OpCode.Return).Operands.Single(),
            Is.SameAs(call.Destination));
    }
}
