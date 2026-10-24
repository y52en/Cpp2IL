using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class AddressedStackSsaTests
{
    static void Increment(ref long value)=>value+=5;
    static void Overwrite(ref long value)=>value=42;
    static void ReadOnly(ref long value){if(value==long.MinValue)throw new Exception("fixture sentinel");}

    [TestCase(true,0L,"Increment",5L)]
    [TestCase(true,37L,"Increment",42L)]
    [TestCase(false,37L,"Increment",42L)]
    [TestCase(true,37L,"Overwrite",42L)]
    [TestCase(false,37L,"Overwrite",42L)]
    [TestCase(true,37L,"ReadOnly",37L)]
    [TestCase(false,37L,"ReadOnly",37L)]
    public void PointerCaptureAndInitializationReferToSameStorageAcrossActualManagedRefCall(bool addressFirst,long initial,string helper,long expected)
    {
        var slot=new Register(700,"stack_-48");var pointer=new Register(4,"X4");var read=new Register(22,"X22");
        var address=new Instruction(0,Cpp2IL.Core.ISIL.OpCode.Move,pointer,new AddressOf(slot));
        var initialize=new Instruction(1,Cpp2IL.Core.ISIL.OpCode.Move,slot,new Immediate(initial));
        var call=new Instruction(2,Cpp2IL.Core.ISIL.OpCode.CallVoid,new StringLiteral(helper),pointer);
        var load=new Instruction(3,Cpp2IL.Core.ISIL.OpCode.Move,read,slot);
        var ret=new Instruction(4,Cpp2IL.Core.ISIL.OpCode.Return,read);
        var graph=new ISILControlFlowGraph(addressFirst?[address,initialize,call,load,ret]:[initialize,address,call,load,ret]);
        SsaForm.Build(graph,new DominatorInfo(graph));
        var captured=(Register)((AddressOf)address.Operands[1]).Target;
        Assert.That(initialize.Destination,Is.EqualTo(captured));
        Assert.That(load.Operands[1],Is.EqualTo(captured));
        Assert.That(captured.Version,Is.EqualTo(-1));
        Assert.That(((Register)address.Destination!).Version,Is.GreaterThanOrEqualTo(1));
        Assert.That(graph.Instructions.Any(i=>i.OpCode==Cpp2IL.Core.ISIL.OpCode.Phi),Is.False);

        // Execute only a newly emitted fixture derived from this SSA graph.
        // No original/native game assembly is loaded or executed.
        var method=new DynamicMethod("StackStorage"+Guid.NewGuid().ToString("N"),typeof(long),Type.EmptyTypes,
            typeof(AddressedStackSsaTests).Module,true);
        var il=method.GetILGenerator();var locals=new Dictionary<Register,LocalBuilder>();
        var pointers=graph.Instructions.Where(i=>i.Operands.Count==2 && i.Operands[1] is AddressOf)
            .Select(i=>(Register)i.Operands[0]).ToHashSet();
        LocalBuilder Local(Register register)
        {
            if(!locals.TryGetValue(register,out var local))
                locals[register]=local=il.DeclareLocal(pointers.Contains(register)?typeof(long).MakeByRefType():typeof(long));
            return local;
        }
        foreach(var instruction in graph.Instructions)
        {
            if(instruction.OpCode==Cpp2IL.Core.ISIL.OpCode.Move)
            {
                switch(instruction.Operands[1])
                {
                    case Immediate value:il.Emit(OpCodes.Ldc_I8,value.Value);break;
                    case Register source:il.Emit(OpCodes.Ldloc,Local(source));break;
                    case AddressOf {Target:Register target}:il.Emit(OpCodes.Ldloca,Local(target));break;
                    default:throw new Exception("unsupported fixture operand");
                }
                il.Emit(OpCodes.Stloc,Local((Register)instruction.Operands[0]));
            }
            else if(instruction.OpCode==Cpp2IL.Core.ISIL.OpCode.CallVoid)
            {
                il.Emit(OpCodes.Ldloc,Local((Register)instruction.Operands[1]));
                il.Emit(OpCodes.Call,typeof(AddressedStackSsaTests).GetMethod(helper,BindingFlags.NonPublic|BindingFlags.Static)!);
            }
            else if(instruction.OpCode==Cpp2IL.Core.ISIL.OpCode.Return)
            {il.Emit(OpCodes.Ldloc,Local((Register)instruction.Operands[0]));il.Emit(OpCodes.Ret);}
        }
        Assert.That(((Func<long>)method.CreateDelegate(typeof(Func<long>)))(),Is.EqualTo(expected));
    }

    [Test]
    public void AddressedStackSlotDoesNotGetPhiButUnaddressedRegistersStillDo()
    {
        var slot=new Register(700,"stack_-48");var value=new Register(8,"X8");var pointer=new Register(4,"X4");var flag=new Register(9,"X9");
        var write=new Instruction(6,Cpp2IL.Core.ISIL.OpCode.Move,slot,new Immediate(9));
        var join=new Instruction(10,Cpp2IL.Core.ISIL.OpCode.Move,new Register(22,"X22"),value);
        var ret=new Instruction(11,Cpp2IL.Core.ISIL.OpCode.Return,slot);
        var graph=new ISILControlFlowGraph([new(0,Cpp2IL.Core.ISIL.OpCode.Move,pointer,new AddressOf(slot)),
            new(1,Cpp2IL.Core.ISIL.OpCode.Move,slot,new Immediate(7)),
            new(2,Cpp2IL.Core.ISIL.OpCode.Move,value,new Immediate(0)),
            new(3,Cpp2IL.Core.ISIL.OpCode.ConditionalJump,write,flag),
            new(4,Cpp2IL.Core.ISIL.OpCode.Jump,join),write,new(7,Cpp2IL.Core.ISIL.OpCode.Move,value,new Immediate(1)),
            new(8,Cpp2IL.Core.ISIL.OpCode.Jump,join),join,ret]);
        SsaForm.Build(graph,new DominatorInfo(graph));
        Assert.That(graph.Instructions.Where(i=>i.OpCode==Cpp2IL.Core.ISIL.OpCode.Phi)
            .Any(i=>((Register)i.Destination!).Number==slot.Number),Is.False);
        Assert.That(((Register)write.Destination!).Version,Is.EqualTo(-1));
        Assert.That(graph.Instructions.Where(i=>i.OpCode==Cpp2IL.Core.ISIL.OpCode.Phi)
            .Any(i=>((Register)i.Destination!).Number==value.Number),Is.True);
    }
}
