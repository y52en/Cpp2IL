using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64StackHfaTests
{
    [TestCase("read",true)]
    [TestCase("partial",false)]
    [TestCase("unknown",false)]
    [TestCase("write",false)]
    [TestCase("address",false)]
    [TestCase("call",false)]
    [TestCase("pointer",false)]
    public void IncomingOverflowHfasRequireExactScalarReadEvidence(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game(); app.InstructionSet=new NewArmV8InstructionSet();
        var vector=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Vector3");
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Test","StackHfa",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var method=owner.InjectMethodContext("Intersect",app.SystemTypes.SystemVoidType,MethodAttributes.Public,[vector,vector,vector,vector]);
        var incoming=app.InstructionSet.CallingConventionResolver!.ResolveForManaged(method);
        Assert.That(incoming[3],Is.EqualTo(new StackOffset(0)));
        Assert.That(incoming[4],Is.EqualTo(new StackOffset(16)));
        method.ParameterOperands=incoming.Select(x=>x is StackOffset s ? (IOperand)new Register(null,"stack_"+s.Offset.ToString("X")) : x).ToList();
        var first=new Instruction(0,OpCode.Move,new Register(null,"V8"),new Register(null,"stack_0")){NativeReadSize=shape=="partial"?2:shape=="unknown"?0:4};
        var second=new Instruction(1,OpCode.Move,new Register(null,"V9"),new Register(null,"stack_4")){NativeReadSize=4};
        var last=new Instruction(2,OpCode.Move,new Register(null,"V10"),new Register(null,"stack_10")){NativeReadSize=4};
        var instructions=new List<Instruction>{first,second,last};
        var root=new Register(null,"stack_0");
        if(shape=="write") instructions.Add(new(3,OpCode.Move,root,new Immediate(0)));
        if(shape=="address") instructions.Add(new(3,OpCode.Move,new Register(null,"X3"),new AddressOf(root)));
        if(shape=="call") instructions.Add(new(3,OpCode.CallVoid,new Immediate(1234),root));
        if(shape=="pointer") instructions.Add(new(3,OpCode.Move,new Register(null,"X3"),new MemoryOperand(root)));
        instructions.Add(new(4,OpCode.Return)); method.ControlFlowGraph=new(instructions);
        // The fourth argument is independently valid even if the third is rejected.
        Assert.That(Arm64HfaRecovery.RecoverIncomingStackHfas(method,incoming),Is.True);
        Assert.That(first.Operands[1] is MemoryOperand,Is.EqualTo(expected));
        Assert.That(second.Operands[1] is MemoryOperand,Is.EqualTo(expected));
        Assert.That(last.Operands[1],Is.TypeOf<MemoryOperand>());
        Assert.That(((Register)method.ParameterOperands[3]).Name,Is.EqualTo(expected?"hfa_stack_arg_2":"stack_0"));
        if(expected)
        {
            Assert.That(((MemoryOperand)second.Operands[1]).Addend,Is.EqualTo(4));
            Assert.That(((MemoryOperand)first.Operands[1]).Base,Is.EqualTo(method.ParameterOperands[3]));
            method.DominatorInfo=new DominatorInfo(method.ControlFlowGraph);
            SsaForm.Build(method);
            LocalVariables.CreateAll(method);
            LocalVariables.ResolveTypesAndFields(method);
            Assert.That(first.Operands[1],Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)first.Operands[1]).Field.Name,Is.EqualTo("x"));
            Assert.That(((FieldReference)second.Operands[1]).Field.Name,Is.EqualTo("y"));
            Assert.That(((LocalVariable)first.Destination!).Type?.FullName,Is.EqualTo("System.Single"));
        }
    }
}
