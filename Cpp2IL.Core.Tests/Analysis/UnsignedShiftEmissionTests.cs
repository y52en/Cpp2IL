using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class UnsignedShiftEmissionTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void ActualGeneratedCilUsesUnsignedShiftAndPreservesTheHighBit(bool wide)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var scalar=wide?t.SystemUInt64Type:t.SystemUInt32Type;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Half",scalar,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("UnsignedShiftFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("UnsignedShiftFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        var signature=wide?module.CorLibTypeFactory.UInt64:module.CorLibTypeFactory.UInt32;
        var method=new MethodDefinition("Half",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(signature,[signature]));
        owner.Methods.Add(method);method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var input=new LocalVariable("input",new Register(null,"X0"),scalar);
        var result=new LocalVariable("result",new Register(null,"X1"),scalar);
        var ilInput=new CilLocalVariable(signature);var ilResult=new CilLocalVariable(signature);
        method.CilMethodBody.LocalVariables.Add(ilInput);method.CilMethodBody.LocalVariables.Add(ilResult);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,ilInput);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{input,ilInput},{result,ilResult}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        emit.Invoke(null,[new Instruction(0,OpCode.ShiftRightUnsigned,result,input,new Immediate(1)){NativeArithmeticSize=wide?8:4},
            context,method,locals,method]);
        emit.Invoke(null,[new Instruction(1,OpCode.Return,result),context,method,locals,method]);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Shr_Un),Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Shr),Is.False);
        using var stream=new MemoryStream();module.Write(stream);
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Half")!;
        foreach(var inputBits in new[]{0x8000000000000000UL,ulong.MaxValue,0x80000000UL})
        {
            object value=wide?(object)inputBits:(uint)inputBits;
            object expected=wide?(object)(inputBits>>1):(uint)inputBits>>1;
            Assert.That(generated.Invoke(null,[value]),Is.EqualTo(expected));
        }
    }
}
