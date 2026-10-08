using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ShiftedArithmeticTests
{
    [TestCase(0x91,8)]
    [TestCase(0x11,4)]
    public void ActualCounterUpdateRetainsNativeArithmeticWidth(byte high,int width)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Counter",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        var native=Disassembler.Disassemble(new byte[]{0xb5,0x06,0x00,high},0x1b0dfbc,new(true,true,false)).Single();
        var emitted=new List<Instruction>();var addresses=new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!.SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!.Invoke(new NewArmV8InstructionSet(),new object[]{native,emitted,addresses,method});
        Assert.That(emitted.Single(i=>i.OpCode==OpCode.Add).NativeArithmeticSize,Is.EqualTo(width));
    }

    [TestCase(0x8b, OpCode.Add, false)]
    [TestCase(0xcb, OpCode.Subtract, false)]
    [TestCase(0xab, OpCode.Add, true)]
    [TestCase(0xeb, OpCode.Subtract, true)]
    public void RealShiftedRegisterEncodingPreservesScale(byte high, OpCode opcode, bool flags)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Shifted",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        // Actual AesCryptUtil.encrypt instruction at RVA 1bfb524: add x8,x8,x9,lsl #4.
        var native = Disassembler.Disassemble(new byte[]{0x08,0x11,0x09,high}, 0x1bfb524, new(true,true,false)).Single();
        var emitted = new List<Instruction>();
        var addresses = new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[]{native, emitted, addresses, method});
        var shift = emitted[0];
        Assert.That(shift.OpCode, Is.EqualTo(OpCode.ShiftLeft));
        Assert.That(((Immediate)shift.Operands[2]).Value, Is.EqualTo(4));
        Assert.That(((Register)shift.Operands[1]).Name, Is.EqualTo("X9"));
        Assert.That(emitted[1].OpCode, Is.EqualTo(opcode));
        Assert.That(emitted[1].Operands[2], Is.EqualTo(shift.Destination));
        Assert.That(addresses.All(a=>a==0x1bfb524), Is.True);
        Assert.That(emitted.Count > 2, Is.EqualTo(flags));
        if (high == 0xeb)
            Assert.That(emitted.Skip(2).Any(i=>i.SourcesAndConstants.Contains(shift.Destination!)), Is.True);
    }
}
