using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeIntegerArithmeticTests
{
    [TestCase(OpCode.Add,8,"Int32","Int64","UInt64")]
    [TestCase(OpCode.Subtract,4,"Int64","UInt32","UInt32")]
    [TestCase(OpCode.Multiply,8,"UInt32","UInt64","UInt64")]
    [TestCase(OpCode.Divide,4,"Int64","Int32",null)]
    [TestCase(OpCode.Add,0,"Int32","Int64",null)]
    [TestCase(OpCode.Add,8,"Object","Int64",null)]
    [TestCase(OpCode.Multiply,8,"Single","Int64",null)]
    [TestCase(OpCode.Add,8,"Boolean","Int64",null)]
    public void NativeWidthIsUsedOnlyForProvenModuloIntegerOperations(OpCode opcode,int width,string from,string to,string? expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var asm=t.SystemObjectType.DeclaringAssembly;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Arithmetic",t.SystemVoidType,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var source=new LocalVariable("input",new Register(null,"X0"),asm.GetTypeByFullName("System."+from));
        var target=new LocalVariable("output",new Register(null,"X1"),asm.GetTypeByFullName("System."+to));
        var i=new Instruction(0,opcode,target,source,new Immediate(1)){NativeArithmeticSize=width};
        Assert.That(IlGenerator.NativeIntegerArithmeticType(i,context)?.FullName,Is.EqualTo(expected==null?null:"System."+expected));
    }
    [TestCase(4,"System.Int32")]
    [TestCase(8,"System.Int64")]
    public void NativeAddWidthTypesTheTemporaryBeforePhiPropagation(int width,string expected)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Arithmetic",t.SystemVoidType,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var source=new LocalVariable("input",new Register(null,"X0"),t.SystemInt32Type);
        var target=new LocalVariable("output",new Register(null,"X1"));
        var i=new Instruction(0,OpCode.Add,target,source,new Immediate(1)){NativeArithmeticSize=width};
        var infer=typeof(LocalVariables).GetMethod("PropagateScalarIntegerArithmetic",BindingFlags.NonPublic|BindingFlags.Static)!;
        Assert.That(infer.Invoke(null,[i,context]),Is.EqualTo(true));
        Assert.That(target.Type?.FullName,Is.EqualTo(expected));
    }
    [TestCase("Int32","Int64",8,OpCode.Add)]
    [TestCase("UInt32","Int64",8,OpCode.Add)]
    [TestCase("Int64","Int32",4,OpCode.Subtract)]
    [TestCase("UInt64","UInt32",4,OpCode.Multiply)]
    [TestCase("UInt32","UInt64",4,OpCode.Add)]
    [TestCase("UInt32","Int64",4,OpCode.Add)]
    [TestCase("UInt32","UInt64",4,OpCode.Negate)]
    [TestCase("UInt64","UInt64",8,OpCode.Negate)]
    public void ActualCilPreservesNativeWidthWithoutEarlyOverflowOrInvalidStack(string from,string to,int width,OpCode op)
        =>RunCilFixture(from,to,width,op);

    [TestCase("Int32",false)]
    [TestCase("UInt32",false)]
    [TestCase("UInt64",false)]
    [TestCase("Int32",true)]
    [TestCase("UInt32",true)]
    [TestCase("UInt64",true)]
    public void ActualCilLongMultiplyUsesNativeInputSignednessNotTheMetadataAlias(string from,bool signed)
        =>RunCilFixture(from,"UInt64",8,OpCode.Multiply,4,signed);

    static void RunCilFixture(string from,string to,int width,OpCode op,int multiplyInputWidth=0,bool signed=false)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;var types=t.SystemObjectType.DeclaringAssembly;
        var fromType=types.GetTypeByFullName("System."+from)!;var toType=types.GetTypeByFullName("System."+to)!;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Calculate",toType,
            System.Reflection.MethodAttributes.Public|System.Reflection.MethodAttributes.Static,[]);
        var assembly=new AssemblyDefinition("NativeWordFixture"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("NativeWordFixture.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        TypeSignature Signature(string name)=>name switch
        {
            "Int32"=>module.CorLibTypeFactory.Int32,"UInt32"=>module.CorLibTypeFactory.UInt32,
            "Int64"=>module.CorLibTypeFactory.Int64,"UInt64"=>module.CorLibTypeFactory.UInt64,_=>throw new ArgumentException()
        };
        var method=new MethodDefinition("Calculate",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(Signature(to),[Signature(from)]));
        owner.Methods.Add(method);method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var input=new LocalVariable("input",new Register(null,"X0"),fromType);
        var result=new LocalVariable("result",new Register(null,"X1"),toType);
        var ilInput=new CilLocalVariable(Signature(from));var ilResult=new CilLocalVariable(Signature(to));
        method.CilMethodBody.LocalVariables.Add(ilInput);method.CilMethodBody.LocalVariables.Add(ilResult);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);method.CilMethodBody.Instructions.Add(CilOpCodes.Stloc,ilInput);
        var locals=new Dictionary<LocalVariable,CilLocalVariable>{{input,ilInput},{result,ilResult}};
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        var operation=op==OpCode.Negate?new Instruction(0,op,result,input):new Instruction(0,op,result,input,new Immediate(3));
        operation.NativeArithmeticSize=width;operation.NativeMultiplyInputSize=multiplyInputWidth;operation.NativeMultiplySigned=signed;
        emit.Invoke(null,[operation,context,method,locals,method]);
        emit.Invoke(null,[new Instruction(1,OpCode.Return,result),context,method,locals,method]);
        using var stream=new MemoryStream();module.Write(stream);
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Calculate")!;
        foreach(var bits in new[]{0UL,0x7fffffffUL,0x80000000UL,uint.MaxValue,ulong.MaxValue})
        {
            object value=from switch{"Int32"=>unchecked((int)bits),"UInt32"=>(uint)bits,"Int64"=>unchecked((long)bits),_=>bits};
            var inputBits=from=="Int32"?unchecked((ulong)(long)(int)bits):from=="UInt32"?(uint)bits:bits;
            if(multiplyInputWidth==4)inputBits=signed?unchecked((ulong)(long)(int)bits):(uint)bits;
            var expected=op switch{OpCode.Add=>unchecked(inputBits+3),OpCode.Subtract=>unchecked(inputBits-3),
                OpCode.Negate=>unchecked(0UL-inputBits),_=>unchecked(inputBits*3)};
            if(width==4)expected=(uint)expected;
            object typedExpected=to switch{"Int32"=>unchecked((int)expected),"UInt32"=>(uint)expected,
                "UInt64"=>expected,_=>unchecked((long)expected)};
            Assert.That(generated.Invoke(null,[value]),Is.EqualTo(typedExpected));
        }
    }

    [TestCase(OpCode.Add,4,0)]
    [TestCase(OpCode.Subtract,4,0)]
    [TestCase(OpCode.Multiply,4,1)]
    [TestCase(OpCode.Multiply,8,1)]
    public void AlgebraicIdentityDoesNotEraseNativeTruncationOrLongMultiplyExtension(OpCode op,int width,long identity)
    {
        var instruction=new Instruction(0,op,new Register(null,"result"),new Register(null,"input"),new Immediate(identity))
            {NativeArithmeticSize=width,NativeMultiplyInputSize=4};
        Assert.That(ConstantFolder.Run(new ISILControlFlowGraph([instruction,new(1,OpCode.Return)])),Is.False);
        Assert.That(instruction.OpCode,Is.EqualTo(op));
    }
    [Test]
    public void ConstantWordNegationZeroExtendsTheResult()
    {
        var instruction=new Instruction(0,OpCode.Negate,new Register(null,"result"),new Immediate(1)){NativeArithmeticSize=4};
        Assert.That(ConstantFolder.Run(new ISILControlFlowGraph([instruction,new(1,OpCode.Return)])),Is.True);
        Assert.That(((Immediate)instruction.Operands[1]).Value,Is.EqualTo(4294967295L));
    }
}
