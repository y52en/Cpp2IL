using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class HiddenStructReturnRecoveryTests
{
    private static Register R(string name)=>new(null,name);
    [TestCase(false)]
    [TestCase(true)]
    public void RealMetadataReturnSizeRequiresUniqueCallee(bool ambiguous)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        app.InstructionSet=new NewArmV8InstructionSet();
        var type=app.Assemblies.SelectMany(a=>a.Types)
            .First(t=>t.IsValueType && TypeSizes.UnboxedSize(t,8)>16);
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","BufferCalls",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var target=owner.InjectMethodContext("ProduceStruct",type,MethodAttributes.Public|MethodAttributes.Static);
        const ulong address=0xDEADBEEF;
        app.MethodsByAddress[address]=ambiguous?[target,target]:[target];
        var caller=owner.InjectMethodContext("Caller",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var call=new Instruction(1,OpCode.Call,new Immediate((long)address),R("X0"));
        caller.ControlFlowGraph=new([new(0,OpCode.Move,R("X8"),new AddressOf(R("stack_-A0"))),call,new(2,OpCode.Return)]);
        Assert.That(HiddenStructReturnRecovery.Run(caller),Is.EqualTo(!ambiguous));
        Assert.That(((Register)call.Destination!).Name,Is.EqualTo(ambiguous?"X0":"stack_-A0"));
        if(!ambiguous) Assert.That(call.ImplicitDefinition?.Name,Is.EqualTo("X0"));
    }

    [Test]
    public void CopiesReadTheSourceBeforeSubsequentRegisterOverwrite()
    {
        var block=new Block();
        block.Instructions.AddRange([
            new(0,OpCode.Move,R("X9"),new AddressOf(R("stack_-A0"))),
            new(1,OpCode.Move,R("X8"),R("X9")),
            new(2,OpCode.Move,R("X9"),new Immediate(0))]);
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,3,R("X8"))?.Name,Is.EqualTo("stack_-A0"));
    }

    [Test]
    public void SinglePredecessorAddressReachesCall()
    {
        var writer=new Block();var call=new Block();call.Predecessors.Add(writer);
        writer.Instructions.Add(new(0,OpCode.Move,R("X8"),new AddressOf(R("stack_-A0"))));
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(call,0,R("X8"))?.Name,Is.EqualTo("stack_-A0"));
    }

    [Test]
    public void JoinOrCycleIsNotGuessed()
    {
        var block=new Block();block.Predecessors.AddRange([new Block(),new Block()]);
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,0,R("X8")),Is.Null);
        block.Predecessors.Clear();block.Predecessors.Add(block);
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,0,R("X8")),Is.Null);
    }

    [TestCase(OpCode.CallVoid)]
    [TestCase(OpCode.IndirectCall)]
    public void InterveningCallsClobberX8(OpCode opcode)
    {
        var block=new Block();
        block.Instructions.Add(new(0,OpCode.Move,R("X8"),new AddressOf(R("stack_-A0"))));
        block.Instructions.Add(opcode==OpCode.CallVoid?new(1,opcode,new Immediate(123)):new(1,opcode,R("X10"),R("X0")));
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,2,R("X8")),Is.Null);
    }

    [Test]
    public void ArbitraryObjectAddressAndArithmeticAreNotStackBuffers()
    {
        var block=new Block();block.Instructions.Add(new(0,OpCode.Move,R("X8"),new AddressOf(R("X19"))));
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,1,R("X8")),Is.Null);
        block.Instructions[0]=new(0,OpCode.Add,R("X8"),R("X19"),new Immediate(16));
        Assert.That(HiddenStructReturnRecovery.ResolveStackAddress(block,1,R("X8")),Is.Null);
    }
}
