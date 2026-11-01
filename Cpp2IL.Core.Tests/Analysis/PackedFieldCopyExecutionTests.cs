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
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedFieldCopyExecutionTests
{
    [TestCase("int32",false)] [TestCase("int32",true)]
    [TestCase("single",false)] [TestCase("single",true)]
    [TestCase("double",false)] [TestCase("double",true)]
    [TestCase("byte",false)] [TestCase("byte",true)]
    [TestCase("boolean",false)] [TestCase("boolean",true)]
    public void OnlyGeneratedFixtureExecutesAndPreservesBitsAndOverlappingCopyOrder(string scalar,bool overlap)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var scalarType=scalar switch {"single"=>t.SystemSingleType,"double"=>t.SystemDoubleType,
            "byte"=>t.SystemByteType,"boolean"=>t.SystemBooleanType,_=>t.SystemInt32Type};
        var laneWidth=scalar is "byte" or "boolean"?1:scalar=="double"?8:4;
        var width=laneWidth==1?4:laneWidth*2;var laneCount=width/laneWidth;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Cell",t.SystemObjectType,TypeAttributes.Public);
        for(var n=0;n<laneCount+1;n++)owner.InjectFieldContext("f"+n,scalarType,FieldAttributes.Public).Offset=16+n*laneWidth;
        var source=new LocalVariable("source",new Register(1,"X1"),owner){ParameterIndex=0};
        var target=new LocalVariable("target",new Register(2,"X2"),owner){ParameterIndex=1};
        var bits=new LocalVariable("bits",new Register(3,"X3"),t.SystemInt64Type);
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Copy",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[owner,owner],["source","target"])
        {
            ParameterLocals=[source,target],Locals=[source,target,bits],
            ControlFlowGraph=new([new(0,OpCode.Move,bits,new MemoryOperand(source,addend:16)){NativeReadSize=width},
                new(1,OpCode.Move,new MemoryOperand(target,addend:16+(overlap?laneWidth:0)),bits){NativeWriteSize=width},new(2,OpCode.Return)])
        };
        Assert.That(PackedPrimitiveFieldCopyRecovery.Recover(context),Is.EqualTo(1));
        var assembly=new AssemblyDefinition("PackedCopy"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("PackedCopy.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var cell=new TypeDefinition("Fixture","Cell",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(cell);owner.PutExtraData("AsmResolverType",cell);
        TypeSignature scalarSignature=scalar switch {"single"=>module.CorLibTypeFactory.Single,"double"=>module.CorLibTypeFactory.Double,
            "byte"=>module.CorLibTypeFactory.Byte,"boolean"=>module.CorLibTypeFactory.Boolean,_=>module.CorLibTypeFactory.Int32};
        foreach(var field in owner.Fields)
        {
            var definition=new FieldDefinition(field.Name,AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,new FieldSignature(scalarSignature));
            cell.Fields.Add(definition);field.PutExtraData("AsmResolverField",definition);
        }
        var constructor=new MethodDefinition(".ctor",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        cell.Methods.Add(constructor);constructor.CilMethodBody=new CilMethodBody();
        constructor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        constructor.CilMethodBody.Instructions.Add(CilOpCodes.Call,module.DefaultImporter.ImportMethod(typeof(object).GetConstructor(Type.EmptyTypes)!));
        constructor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var cellSignature=new TypeDefOrRefSignature(cell,false);
        var method=new MethodDefinition("Copy",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,[cellSignature,cellSignature]));
        cell.Methods.Add(method);method.ParameterDefinitions.Add(new ParameterDefinition(1,"source",0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2,"target",0));
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var locals=new Dictionary<LocalVariable,CilLocalVariable>();
        foreach(var local in context.Locals)
        {
            var signature=ReferenceEquals(local.Type,owner)?(TypeSignature)cellSignature:
                ReferenceEquals(local,bits)?module.CorLibTypeFactory.Int64:scalarSignature;
            var slot=new CilLocalVariable(signature);locals[local]=slot;method.CilMethodBody.LocalVariables.Add(slot);
        }
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in context.ControlFlowGraph.Instructions)emit.Invoke(null,[instruction,context,method,locals,method]);
        using var stream=new MemoryStream();module.Write(stream);
        // No original binary/game code is executed. Only this small new CIL fixture.
        var generated=Assembly.Load(stream.ToArray()).GetType("Fixture.Cell")!;
        var first=Activator.CreateInstance(generated)!;var second=overlap?first:Activator.CreateInstance(generated)!;
        object Value(int n)=>scalar switch
        {
            "single"=>n==0?BitConverter.Int32BitsToSingle(unchecked((int)0x7fc12345)):n==1?BitConverter.Int32BitsToSingle(unchecked((int)0x80000000)):17.25f,
            "double"=>n==0?BitConverter.Int64BitsToDouble(unchecked((long)0x7ff8123456789abc)):n==1?BitConverter.Int64BitsToDouble(unchecked((long)0x8000000000000000)):17.25d,
            "byte"=>(byte)(201+n),"boolean"=>n%2==0,_=>unchecked((int)0x9abcdef0)+n
        };
        object Bits(object value)=>value switch {float f=>BitConverter.SingleToInt32Bits(f),double d=>BitConverter.DoubleToInt64Bits(d),_=>value};
        for(var n=0;n<laneCount+1;n++)generated.GetField("f"+n)!.SetValue(first,Value(n));
        var before=Enumerable.Range(0,laneCount).Select(n=>Bits(generated.GetField("f"+n)!.GetValue(first)!)).ToArray();
        generated.GetMethod("Copy")!.Invoke(null,[first,second]);
        for(var n=0;n<laneCount;n++)Assert.That(Bits(generated.GetField("f"+(n+(overlap?1:0)))!.GetValue(second)!),Is.EqualTo(before[n]));
    }
}
