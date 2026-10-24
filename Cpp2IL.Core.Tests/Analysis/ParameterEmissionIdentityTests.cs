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

public class ParameterEmissionIdentityTests
{
    static readonly MethodInfo Emit=typeof(IlGenerator).GetMethod("GenerateInstructions",BindingFlags.NonPublic|BindingFlags.Static)!;
    static (ModuleDefinition Module,TypeDefinition Owner) Module()
    {
        var assembly=new AssemblyDefinition("ParameterIdentity"+Guid.NewGuid().ToString("N"),new Version(1,0));
        var module=new ModuleDefinition("ParameterIdentity.dll",new AssemblyReference("mscorlib",new Version(4,0,0,0)));
        assembly.Modules.Add(module);
        var owner=new TypeDefinition("Fixture","Generated",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(owner);return(module,owner);
    }
    static MethodInfo Load(ModuleDefinition module)
    {
        using var stream=new MemoryStream();module.Write(stream);
        return Assembly.Load(stream.ToArray()).GetType("Fixture.Generated")!.GetMethod("Run")!;
    }
    [TestCase("Int32")]
    [TestCase("Single")]
    [TestCase("String")]
    public void SameDisplayNameDoesNotLoadAnUnrelatedArgument(string kind)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var scalar=kind=="Int32"?t.SystemInt32Type:kind=="Single"?t.SystemSingleType:t.SystemStringType;
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Run",scalar,
            MethodAttributes.Public|MethodAttributes.Static,[scalar],["v0"]);
        var (module,owner)=Module();
        var type=kind=="Int32"?module.CorLibTypeFactory.Int32:kind=="Single"?module.CorLibTypeFactory.Single:module.CorLibTypeFactory.String;
        var method=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(type,[type]));
        owner.Methods.Add(method);method.ParameterDefinitions.Add(new ParameterDefinition(1,"v0",0));
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var input=new LocalVariable("v0",new Register(null,"X0"),scalar);
        var temp=new LocalVariable("v0",new Register(null,"X1"),scalar);
        context.ParameterLocals=[input];context.Locals=[input,temp];
        var locals=new Dictionary<LocalVariable,CilLocalVariable>();
        foreach(var local in context.Locals){var slot=new CilLocalVariable(type);locals[local]=slot;method.CilMethodBody.LocalVariables.Add(slot);}
        IOperand value=kind=="Int32"?new Immediate(42):kind=="Single"?new FloatLiteral(42.5f):new StringLiteral("local value");
        Emit.Invoke(null,[new Instruction(0,OpCode.Move,temp,value),context,method,locals,method]);
        Emit.Invoke(null,[new Instruction(1,OpCode.Return,temp),context,method,locals,method]);
        Assert.That(temp.ParameterIndex,Is.EqualTo(-1));Assert.That(input.ParameterIndex,Is.EqualTo(0));
        Assert.That(method.CilMethodBody.Instructions.Any(i=>i.OpCode==CilOpCodes.Ldarg),Is.False);
        object argument=kind=="Int32"?(object)17:kind=="Single"?17.5f:"argument value";
        object expected=kind=="Int32"?(object)42:kind=="Single"?42.5f:"local value";
        Assert.That(Load(module).Invoke(null,[argument]),Is.EqualTo(expected));
    }
    [TestCase(0,false)]
    [TestCase(1,false)]
    [TestCase(0,true)]
    [TestCase(1,true)]
    public void ExplicitIncomingOrdinalSurvivesManagedAndLocalDisplayNameChanges(int ordinal,bool instance)
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;var (module,owner)=Module();
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Run",t.SystemInt32Type,
            MethodAttributes.Public|(instance?0:MethodAttributes.Static),[t.SystemInt32Type,t.SystemInt32Type],["originalA","originalB"]);
        var signature=instance?MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32,
            [module.CorLibTypeFactory.Int32,module.CorLibTypeFactory.Int32])
            :MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,[module.CorLibTypeFactory.Int32,module.CorLibTypeFactory.Int32]);
        var method=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |(instance?0:AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static),signature);owner.Methods.Add(method);
        if(instance)
        {
            var ctor=new MethodDefinition(".ctor",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
                MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));owner.Methods.Add(ctor);
            ctor.CilMethodBody=new CilMethodBody();ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
            ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call,module.CorLibTypeFactory.Object.Type.CreateMemberReference(".ctor",MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)));
            ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        }
        method.ParameterDefinitions.Add(new ParameterDefinition(1,"renamedA",0));method.ParameterDefinitions.Add(new ParameterDefinition(2,"renamedB",0));
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var input=new LocalVariable("unrelated_display_name",new Register(null,"input"),t.SystemInt32Type){ParameterIndex=ordinal};
        context.ParameterLocals=[input];context.Locals=[input];
        var slot=new CilLocalVariable(module.CorLibTypeFactory.Int32);method.CilMethodBody.LocalVariables.Add(slot);
        Emit.Invoke(null,[new Instruction(0,OpCode.Return,input),context,method,new Dictionary<LocalVariable,CilLocalVariable>{{input,slot}},method]);
        var execute=Load(module);var receiver=instance?Activator.CreateInstance(execute.DeclaringType!):null;
        Assert.That(execute.Invoke(receiver,[17,413]),Is.EqualTo(ordinal==0?17:413));
    }
    [Test]
    public void SameNamedStructLocalStoresDoNotMutateTheActualValueParameter()
    {
        var t=TestGameLoader.LoadSimple2019Game().SystemTypes;var (module,owner)=Module();
        var pair=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Fixture","Pair",t.SystemValueTypeType,
            TypeAttributes.Public|TypeAttributes.SequentialLayout);
        var field=new InjectedFieldAnalysisContext("X",t.SystemInt32Type,FieldAttributes.Public,pair,0);pair.Fields.Add(field);
        var managed=new TypeDefinition("Fixture","Pair",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.SequentialLayout|AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System","ValueType"));module.TopLevelTypes.Add(managed);
        var managedField=new FieldDefinition("X",AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,new FieldSignature(module.CorLibTypeFactory.Int32));
        managed.Fields.Add(managedField);pair.PutExtraData("AsmResolverType",managed);field.PutExtraData("AsmResolverField",managedField);
        var pairSignature=managed.ToTypeSignature(true);
        var method=new MethodDefinition("Run",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            |AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,[pairSignature]));
        owner.Methods.Add(method);method.ParameterDefinitions.Add(new ParameterDefinition(1,"v0",0));
        method.CilMethodBody=new CilMethodBody{InitializeLocals=true};
        var context=new InjectedMethodAnalysisContext(t.SystemObjectType,"Run",t.SystemInt32Type,
            MethodAttributes.Public|MethodAttributes.Static,[pair],["v0"]);
        var input=new LocalVariable("v0",new Register(null,"input"),pair);var temp=new LocalVariable("v0",new Register(null,"temp"),pair);
        context.ParameterLocals=[input];context.Locals=[input,temp];var locals=new Dictionary<LocalVariable,CilLocalVariable>();
        foreach(var local in context.Locals){var slot=new CilLocalVariable(pairSignature);locals[local]=slot;method.CilMethodBody.LocalVariables.Add(slot);}
        Emit.Invoke(null,[new Instruction(0,OpCode.Move,temp,new DefaultStructValue(pair)),context,method,locals,method]);
        Emit.Invoke(null,[new Instruction(1,OpCode.Move,new FieldReference(field,temp,0),new Immediate(42)),context,method,locals,method]);
        Emit.Invoke(null,[new Instruction(2,OpCode.Return,new FieldReference(field,input,0)),context,method,locals,method]);
        var run=Load(module);var value=Activator.CreateInstance(run.GetParameters()[0].ParameterType)!;
        value.GetType().GetField("X")!.SetValue(value,17);
        Assert.That(run.Invoke(null,[value]),Is.EqualTo(17));
    }
}
