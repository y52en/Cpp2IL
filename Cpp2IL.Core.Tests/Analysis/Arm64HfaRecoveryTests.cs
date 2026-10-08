using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64HfaRecoveryTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void ScalarFloatIsNotAnAggregate(bool useDouble)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        Assert.That(Arm64HfaLayout.Fields(useDouble?app.SystemTypes.SystemDoubleType:app.SystemTypes.SystemSingleType),Is.Null);
    }

    [Test]
    public void RealVector3MetadataUsesThreeFloatingLanes()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var fields=Arm64HfaLayout.Fields(vector);
        Assert.That(fields,Is.Not.Null);
        Assert.That(fields!.Select(f=>f.Offset),Is.EqualTo(new[]{0,4,8}));
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","HfaCalls",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var target=owner.InjectMethodContext("Subtract",vector,MethodAttributes.Public|MethodAttributes.Static,[vector,vector,app.SystemTypes.SystemSingleType]);
        var resolver=new Arm64CallingConventionResolver();
        Assert.That(resolver.ReturnRegister(target).Name,Is.EqualTo("V0"));
        Assert.That(resolver.ReturnsViaHiddenBuffer(target),Is.False);
        var operands=resolver.ResolveForManaged(target);
        Assert.That(((Register)operands[0]).Name,Is.EqualTo("hfa_arg_0"));
        Assert.That(((Register)operands[1]).Name,Is.EqualTo("hfa_arg_1"));
        Assert.That(((Register)operands[2]).Name,Is.EqualTo("V6"));
        Assert.That(((Register)operands[3]).Name,Is.EqualTo("X0"));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void CallerPacksArgumentsAndProjectsEveryReturnLane(bool ambiguous)
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","HfaCalls",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var target=owner.InjectMethodContext("Subtract",vector,MethodAttributes.Public|MethodAttributes.Static,[vector,vector]);
        const ulong address=0xDEADBEEF;app.MethodsByAddress[address]=ambiguous?[target,target]:[target];
        var caller=owner.InjectMethodContext("Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var call=new Instruction(0,OpCode.Call,new Immediate((long)address),new Register(null,"V0"));
        call.AddOperands(new Arm64CallingConventionResolver().ResolveForManaged(target));
        caller.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        Assert.That(Arm64HfaRecovery.Run(caller),Is.EqualTo(!ambiguous));
        if(ambiguous) return;
        var instructions=caller.ControlFlowGraph.Instructions;
        Assert.That(instructions.Count(i=>i is {OpCode:OpCode.Move,Operands:[_,DefaultStructValue]}),Is.EqualTo(2));
        Assert.That(instructions.Count(i=>i is {OpCode:OpCode.Move,Operands:[MemoryOperand,_]}),Is.EqualTo(6));
        Assert.That(instructions.Where(i=>i is {OpCode:OpCode.Move,Operands:[Register,MemoryOperand]}).Select(i=>((Register)i.Destination!).Name),Is.EqualTo(new[]{"V0","V1","V2"}));
        Assert.That(((Register)call.Destination!).Name,Does.StartWith("hfa_result_"));
    }

    [Test]
    public void CalleeProjectsIncomingVectorAndPacksReturn()
    {
        var app=TestGameLoader.LoadSimple2019Game();app.InstructionSet=new NewArmV8InstructionSet();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","HfaCalls",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var method=owner.InjectMethodContext("Identity",vector,MethodAttributes.Public|MethodAttributes.Static,[vector]);
        var ret=new Instruction(0,OpCode.Return,new Register(null,"V0"));method.ControlFlowGraph=new([ret]);
        Assert.That(Arm64HfaRecovery.Run(method),Is.True);
        var instructions=method.ControlFlowGraph.Instructions;
        Assert.That(instructions.Count(i=>i is {OpCode:OpCode.Move,Operands:[Register,MemoryOperand]}),Is.EqualTo(3));
        Assert.That(instructions.Count(i=>i is {OpCode:OpCode.Move,Operands:[MemoryOperand,Register]}),Is.EqualTo(3));
        Assert.That(((Register)ret.Operands[0]).Name,Does.StartWith("hfa_return_"));
    }
}
