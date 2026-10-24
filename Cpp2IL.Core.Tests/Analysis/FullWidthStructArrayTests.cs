using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.IO;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class FullWidthStructArrayTests
{
    internal static (MethodAnalysisContext Method,Instruction Access,TypeAnalysisContext Wrapper,FieldAnalysisContext Field) Create(
        bool store,bool dynamicIndex,bool whole,int size=4,string shape="valid")
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var scalar=size==4?t.SystemInt32Type:t.SystemInt64Type;
        var wrapper=app.Assemblies.SelectMany(a=>a.Types).Where(type=>type.IsValueType && !type.IsEnumType
            && !TypeSizes.IsScalarValueType(type) && !type.HasAnyGenericParameters() && TypeSizes.UnboxedSize(type,8)==size)
            .Where(type=>type.Fields.Count(f=>!f.IsStatic)==1)
            .Where(type=>type.Fields.Single(f=>!f.IsStatic) is {Offset:0} field && ReferenceEquals(field.FieldType,scalar))
            .OrderBy(type=>type.FullName).First();
        var field=wrapper.Fields.Single(f=>!f.IsStatic);
        if(shape=="overlap")wrapper.Fields.Add(new InjectedFieldAnalysisContext("overlap",scalar,FieldAttributes.Public,wrapper,0));
        var array=new LocalVariable("array",new(null,"X19"),new SzArrayTypeAnalysisContext(wrapper)){ParameterIndex=0};
        var index=new LocalVariable("index",new(null,"X1"),t.SystemInt32Type){ParameterIndex=1};
        var value=new LocalVariable("value",new(null,"X2"),whole?wrapper:scalar){ParameterIndex=store?2:-1};
        var other=new LocalVariable("other",new(null,"X3"),array.Type){ParameterIndex=3};
        var scaled=new LocalVariable("scaled",new(null,"scaled"));var address=new LocalVariable("address",new(null,"address"));
        var width=shape=="partial"?size/2:shape=="cross-element"?size*2:size;
        var offset=shape=="header"?24:32+(dynamicIndex?0:2*size);
        var memory=new MemoryOperand(dynamicIndex?address:array,addend:offset);
        var access=store?new Instruction(2,OpCode.Move,memory,value){NativeWriteSize=width}
            :new Instruction(2,OpCode.Move,value,memory){NativeReadSize=width};
        var code=new List<Instruction>();
        if(dynamicIndex)
        {
            code.Add(new(0,OpCode.Multiply,scaled,index,new Immediate(shape=="wrong-stride"?size*2:size)));
            code.Add(new(1,OpCode.Add,address,array,scaled));
        }
        if(shape=="array-reassigned")code.Add(new(4,OpCode.Move,array,other));
        if(shape=="index-reassigned")code.Add(new(4,OpCode.Move,index,new Immediate(0)));
        code.Add(access);code.Add(store?new(3,OpCode.Return):new(3,OpCode.Return,value));
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Access",store?t.SystemVoidType:value.Type!,
            MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=new(code),Locals=[array,index,value,other,scaled,address],ParameterLocals=[array,index,other]};
        if(store)method.ParameterLocals.Add(value);
        if(shape=="unknown-value")value.Type=null;
        if(shape=="wrong-value")value.Type=t.SystemDoubleType;
        if(shape=="unbound-array")method.ParameterLocals.Remove(array);
        if(shape=="unbound-index")method.ParameterLocals.Remove(index);
        return(method,access,wrapper,field);
    }

    private static IEnumerable<TestCaseData> Positives()
    {
        foreach(var size in new[]{4,8})foreach(var store in new[]{false,true})
        foreach(var dynamicIndex in new[]{false,true})foreach(var whole in new[]{false,true})
            yield return new TestCaseData(store,dynamicIndex,whole,size);
    }

    [TestCaseSource(nameof(Positives))]
    public void ExactWholeElementOrSingleScalarFieldKeepsManagedArrayStorage(bool store,bool dynamicIndex,bool whole,int size)
    {
        var(method,access,_,field)=Create(store,dynamicIndex,whole,size);
        Assert.That(ArrayRecovery.RecoverStructComponents(method),Is.True);
        if(whole)Assert.That(access.Operands[store?0:1],Is.TypeOf<ArrayAccess>());
        else
        {
            var actual=(FieldReference)access.Operands[store?0:1];Assert.That(actual.Field,Is.SameAs(field));
            var prefix=method.ControlFlowGraph!.Instructions.Single(i=>ReferenceEquals(i.Destination,actual.Local));
            Assert.That(prefix.Operands[1],Is.TypeOf<AddressOf>());
        }
        Assert.That(ArrayRecovery.RecoverStructComponents(method),Is.False);
    }

    [TestCase("partial")] [TestCase("cross-element")] [TestCase("header")]
    [TestCase("wrong-stride")] [TestCase("unknown-value")] [TestCase("wrong-value")]
    [TestCase("unbound-array")] [TestCase("unbound-index")] [TestCase("array-reassigned")]
    [TestCase("index-reassigned")] [TestCase("overlap")]
    public void AmbiguousWidthTypeOrStaleAddressRemainsDiagnostic(string shape)
    {
        foreach(var store in new[]{false,true})
        {
            var(method,access,_,_)=Create(store,true,false,4,shape);
            Assert.That(ArrayRecovery.RecoverStructComponents(method),Is.False,shape);
            Assert.That(access.Operands[store?0:1],Is.TypeOf<MemoryOperand>());
        }
    }

    [TestCase(false,false)] [TestCase(true,false)]
    [TestCase(false,true)] [TestCase(true,true)]
    public void ActualGeneratedCilUpdatesRealStorageAndRetainsNullAndBounds(bool store,bool whole)
    {
        var(context,access,wrapper,field)=Create(store,true,whole);
        Assert.That(ArrayRecovery.RecoverStructComponents(context),Is.True);
        var module=new ModuleDefinition("FullWidthArray.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        var assembly=new AssemblyDefinition("FullWidthArray"+Guid.NewGuid().ToString("N"),new Version(1,0));assembly.Modules.Add(module);
        var wrapperDef=new TypeDefinition("Fixture","Wrapper",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System","ValueType"));module.TopLevelTypes.Add(wrapperDef);
        wrapper.PutExtraData("AsmResolverType",wrapperDef);
        var fieldDef=new FieldDefinition("Value",AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.Int32));wrapperDef.Fields.Add(fieldDef);field.PutExtraData("AsmResolverField",fieldDef);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);
        TypeSignature valueType=whole?wrapperDef.ToTypeSignature():module.CorLibTypeFactory.Int32;
        var parameters=new List<TypeSignature>{new SzArrayTypeSignature(wrapperDef.ToTypeSignature()),module.CorLibTypeFactory.Int32};
        if(store)parameters.Add(valueType);
        var method=new MethodDefinition("Access",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(store?module.CorLibTypeFactory.Void:valueType,parameters.ToArray()));owner.Methods.Add(method);
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var locals=new Dictionary<LocalVariable,CilLocalVariable>();
        if(!whole)
        {
            var address=((FieldReference)access.Operands[store?0:1]).Local;
            var slot=new CilLocalVariable(new ByReferenceTypeSignature(wrapperDef.ToTypeSignature()));
            locals.Add(address,slot);method.CilMethodBody.LocalVariables.Add(slot);
        }
        if(!store)
        {
            var slot=new CilLocalVariable(valueType);locals.Add((LocalVariable)access.Operands[0],slot);
            method.CilMethodBody.LocalVariables.Add(slot);
        }
        DeadCodeEliminator.Run(context);
        var emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
        foreach(var instruction in context.ControlFlowGraph!.Instructions.Where(i=>i.OpCode!=OpCode.Nop))
            emit.Invoke(null,[instruction,context,method,locals,method]);
        using var stream=new MemoryStream();module.Write(stream);var runtime=Assembly.Load(stream.ToArray());
        var wrapperType=runtime.GetType("Fixture.Wrapper")!;var runtimeField=wrapperType.GetField("Value")!;
        object Wrapped(int value){var result=Activator.CreateInstance(wrapperType)!;runtimeField.SetValue(result,value);return result;}
        var array=Array.CreateInstance(wrapperType,2);array.SetValue(Wrapped(11),0);array.SetValue(Wrapped(22),1);
        var execute=runtime.GetType("Fixture.Generated")!.GetMethod("Access")!;
        object?[] Arguments(object? target,int index)=>store?[target,index,whole?Wrapped(99):(object)99]:[target,index];
        var observed=execute.Invoke(null,Arguments(array,1));
        if(!store)Assert.That(whole?runtimeField.GetValue(observed):observed,Is.EqualTo(22));
        Assert.That(runtimeField.GetValue(array.GetValue(0)),Is.EqualTo(11));
        Assert.That(runtimeField.GetValue(array.GetValue(1)),Is.EqualTo(store?99:22));
        var nullError=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,Arguments(null,0)));
        Assert.That(nullError!.InnerException,Is.TypeOf<NullReferenceException>());
        foreach(var index in new[]{-1,2})
        {
            var error=Assert.Throws<TargetInvocationException>(()=>execute.Invoke(null,Arguments(array,index)));
            Assert.That(error!.InnerException,Is.TypeOf<IndexOutOfRangeException>());
        }
    }
}
