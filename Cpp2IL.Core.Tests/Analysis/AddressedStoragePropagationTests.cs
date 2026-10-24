using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using OpCode=Cpp2IL.Core.ISIL.OpCode;

namespace Cpp2IL.Core.Tests.Analysis;

public class AddressedStoragePropagationTests
{
    static void Increment(ref long value)=>value+=5;

    [TestCase(true,true,0L)]
    [TestCase(true,true,37L)]
    [TestCase(true,false,0L)]
    [TestCase(true,false,37L)]
    [TestCase(false,true,0L)]
    [TestCase(false,true,37L)]
    [TestCase(false,false,0L)]
    [TestCase(false,false,37L)]
    public void RefCallReadsCurrentStorageButSnapshotDoesNotFollowLaterWrites(bool addressFirst,bool indirect,long initial)
    {
        var slot=new LocalVariable("slot",new Register(700,"stack_-48"));
        var pointer=new LocalVariable("pointer",new Register(4,"X4"));
        var snapshot=new LocalVariable("snapshot",new Register(22,"X22"));
        var address=new Instruction(0,OpCode.Move,pointer,new AddressOf(slot));
        var initialize=new Instruction(1,OpCode.Move,slot,new Immediate(initial));
        IOperand argument=indirect?pointer:new AddressOf(slot);
        var call=new Instruction(2,OpCode.CallVoid,new StringLiteral("Increment"),argument);
        var capture=new Instruction(3,OpCode.Move,snapshot,slot);
        var again=new Instruction(4,OpCode.CallVoid,new StringLiteral("Increment"),argument);
        var ret=new Instruction(5,OpCode.Return,snapshot);
        var instructions=new List<Instruction>();
        if(indirect && addressFirst)instructions.Add(address);
        instructions.Add(initialize);
        if(indirect && !addressFirst)instructions.Add(address);
        instructions.AddRange([call,capture,again,ret]);
        var graph=new ISILControlFlowGraph(instructions);
        SsaSimplifier.Run(graph,[]);
        Assert.That(initialize.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(capture.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(capture.Operands[1],Is.SameAs(slot));
        Assert.That(ret.Operands[0],Is.SameAs(snapshot));

        // Only this newly emitted synthetic fixture executes, never a game DLL.
        var method=new DynamicMethod("RefSnapshot"+Guid.NewGuid().ToString("N"),typeof(long),Type.EmptyTypes,
            typeof(AddressedStoragePropagationTests).Module,true);
        var il=method.GetILGenerator();var locals=new Dictionary<LocalVariable,LocalBuilder>();
        LocalBuilder Local(LocalVariable local)
        {
            if(!locals.TryGetValue(local,out var result))
                locals[local]=result=il.DeclareLocal(ReferenceEquals(local,pointer)?typeof(long).MakeByRefType():typeof(long));
            return result;
        }
        void Load(IOperand operand)
        {
            switch(operand)
            {
                case Immediate value:il.Emit(OpCodes.Ldc_I8,value.Value);break;
                case LocalVariable local:il.Emit(OpCodes.Ldloc,Local(local));break;
                case AddressOf {Target:LocalVariable target}:il.Emit(OpCodes.Ldloca,Local(target));break;
                default:throw new Exception("unsupported fixture operand");
            }
        }
        foreach(var instruction in graph.Instructions)
        {
            if(instruction.OpCode==OpCode.Move)
            {Load(instruction.Operands[1]);il.Emit(OpCodes.Stloc,Local((LocalVariable)instruction.Operands[0]));}
            else if(instruction.OpCode==OpCode.CallVoid)
            {
                Load(instruction.Operands[1]);
                il.Emit(OpCodes.Call,typeof(AddressedStoragePropagationTests).GetMethod("Increment",BindingFlags.NonPublic|BindingFlags.Static)!);
            }
            else if(instruction.OpCode==OpCode.Return){Load(instruction.Operands[0]);il.Emit(OpCodes.Ret);}
        }
        Assert.That(((Func<long>)method.CreateDelegate(typeof(Func<long>)))(),Is.EqualTo(initial+5),
            "the first ref call changes the read, while the second must not retroactively change its snapshot");
    }
}
