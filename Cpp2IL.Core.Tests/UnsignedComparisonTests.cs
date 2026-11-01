using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using AsmTypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using AsmMethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class UnsignedComparisonTests
{
    [TestCase(OpCode.CheckLess, false, false)]
    [TestCase(OpCode.CheckGreater, false, false)]
    [TestCase(OpCode.CheckLessOrEqual, false, false)]
    [TestCase(OpCode.CheckGreaterOrEqual, false, false)]
    [TestCase(OpCode.CheckLess, true, false)]
    [TestCase(OpCode.CheckGreater, true, false)]
    [TestCase(OpCode.CheckLessOrEqual, true, false)]
    [TestCase(OpCode.CheckGreaterOrEqual, true, false)]
    [TestCase(OpCode.CheckLess, false, true)]
    [TestCase(OpCode.CheckGreater, false, true)]
    [TestCase(OpCode.CheckLessOrEqual, false, true)]
    [TestCase(OpCode.CheckGreaterOrEqual, false, true)]
    [TestCase(OpCode.CheckLess, true, true)]
    [TestCase(OpCode.CheckGreater, true, true)]
    [TestCase(OpCode.CheckLessOrEqual, true, true)]
    [TestCase(OpCode.CheckGreaterOrEqual, true, true)]
    public void ActuallyGeneratedManagedIlPreservesSignednessAtBitBoundaries(OpCode opcode, bool unsigned, bool wide)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var input=wide ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemInt32Type;
        var left=new LocalVariable("left",new Register(null,"X0"),input);
        var right=new LocalVariable("right",new Register(null,"X1"),input);
        var result=new LocalVariable("result",new Register(null,"C"),app.SystemTypes.SystemBooleanType);
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Compare",app.SystemTypes.SystemBooleanType,MethodAttributes.Public|MethodAttributes.Static,[input,input]);
        caller.ControlFlowGraph=new([new Instruction(0,opcode,result,left,right){UnsignedComparison=unsigned},new(1,OpCode.Return,result)]);
        caller.Locals=[left,right,result];caller.ParameterLocals=[left,right];caller.AnalysisWarnings=[];
        var assembly=new AssemblyDefinition("UnsignedTest"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("UnsignedTest.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));assembly.Modules.Add(module);
        var type=new TypeDefinition("Test","Generated",AsmTypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var scalar=wide ? module.CorLibTypeFactory.Int64 : module.CorLibTypeFactory.Int32;
        var method=new MethodDefinition("Compare",AsmMethodAttributes.Public|AsmMethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Boolean,[scalar,scalar]));type.Methods.Add(method);
        // Exercise the actual instruction emitter and execute its output.
        // The tiny fixture supplies CLR primitive signatures directly instead
        // of pretending the game's complete corlib was exported into this DLL.
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"left",0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2,"right",0));
        method.CilMethodBody=new CilMethodBody(){InitializeLocals=true};
        var booleanLocal=new CilLocalVariable(module.CorLibTypeFactory.Boolean);
        method.CilMethodBody.LocalVariables.Add(booleanLocal);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{result,booleanLocal}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[new Instruction(0,opcode,result,left,right){UnsignedComparison=unsigned},caller,method,locals,method]);
        emit.Invoke(null,[new Instruction(1,OpCode.Return,result),caller,method,locals,method]);
        var compare=method.CilMethodBody!.Instructions.Single(i=>i.OpCode is var op && (op==CilOpCodes.Clt || op==CilOpCodes.Clt_Un || op==CilOpCodes.Cgt || op==CilOpCodes.Cgt_Un));
        Assert.That(compare.OpCode==CilOpCodes.Clt_Un || compare.OpCode==CilOpCodes.Cgt_Un,Is.EqualTo(unsigned));
        using var stream=new MemoryStream();module.Write(stream);
        var generated=System.Reflection.Assembly.Load(stream.ToArray()).GetType("Test.Generated")!.GetMethod("Compare")!;
        var pairs=new(long,long)[]{(-1,9),(0,0),(0,9),(9,0),(long.MinValue,0),(int.MinValue,0),(long.MaxValue,9)};
        foreach(var (a,b) in pairs)
        {
            var x=wide ? a : unchecked((int)a);var y=wide ? b : unchecked((int)b);
            var comparison=unsigned ? (wide ? unchecked((ulong)x).CompareTo(unchecked((ulong)y)) : unchecked((uint)x).CompareTo(unchecked((uint)y))) : x.CompareTo(y);
            var expected=opcode switch {OpCode.CheckLess=>comparison<0,OpCode.CheckGreater=>comparison>0,OpCode.CheckLessOrEqual=>comparison<=0,_=>comparison>=0};
            object px=wide ? (object)x : (int)x;object py=wide ? (object)y : (int)y;
            Assert.That(generated.Invoke(null,[px,py]),Is.EqualTo(expected),$"{x},{y}");
        }
    }

    [TestCase(0x71)]
    [TestCase(0xf1)]
    public void ActualCmpCarryUsesUnsignedBorrowButSignFlagRemainsSigned(byte high)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Cmp",app.SystemTypes.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[]);
        // cmp w8,9 from the proven signup switch; high F1 is cmp x8,9.
        var native=Disassembler.Disassemble(new byte[]{0x1f,0x25,0x00,high},0x182fb60,new(true,true,false)).Single();
        var emitted=new List<Instruction>();var addresses=new List<ulong>();
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets",BindingFlags.NonPublic|BindingFlags.Static)!.SetValue(null,new Dictionary<string,ulong>());
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement",BindingFlags.NonPublic|BindingFlags.Instance)!.Invoke(new NewArmV8InstructionSet(),new object[]{native,emitted,addresses,caller});
        Assert.That(emitted.Single(i=>i.OpCode==OpCode.CheckLess && i.Operands[0] is Register{Name:"C"}).UnsignedComparison,Is.True);
        Assert.That(emitted.Single(i=>i.OpCode==OpCode.CheckLess && i.Operands[0] is Register{Name:"N"}).UnsignedComparison,Is.False);
    }

    [Test]
    public void UnsignedCompareAgainstZeroIsNotMistakenForSignedSubtractSignFlag()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var a=new LocalVariable("a",new Register(null,"X0"),app.SystemTypes.SystemInt32Type);
        var b=new LocalVariable("b",new Register(null,"X1"),app.SystemTypes.SystemInt32Type);
        var delta=new LocalVariable("delta",new Register(null,"T"),app.SystemTypes.SystemInt32Type);
        var carry=new LocalVariable("carry",new Register(null,"C"),app.SystemTypes.SystemBooleanType);
        var compare=new Instruction(1,OpCode.CheckLess,carry,delta,new Immediate(0)){UnsignedComparison=true};
        var exit=new Instruction(3,OpCode.Return);
        var cfg=new Cpp2IL.Core.Graphs.ISILControlFlowGraph([new(0,OpCode.Subtract,delta,a,b),compare,new(2,OpCode.ConditionalJump,exit,carry),exit]);
        FlagConditionRecovery.Run(cfg);
        Assert.That(compare.UnsignedComparison,Is.True);
        Assert.That(compare.Operands[1],Is.SameAs(delta));
    }
}
