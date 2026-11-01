using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackFieldZeroRecoveryTests
{
    [TestCase("exact")]
    [TestCase("copied")]
    [TestCase("whole")]
    [TestCase("mismatch")]
    [TestCase("ambiguous")]
    [TestCase("nonstack")]
    [TestCase("notcall")]
    [TestCase("escaped")]
    [TestCase("fieldwrite")]
    public void OnlyExactScalarParameterAndProvenStackCallResultAreProjected(string shape)
    {
        var types=TestGameLoader.LoadSimple2019Game().SystemTypes;
        var type=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Data",types.SystemValueTypeType,TypeAttributes.Public);
        var field=new InjectedFieldAnalysisContext("id",types.SystemInt32Type,FieldAttributes.Public,type){Offset=0};
        type.Fields.Add(field);
        if(shape=="ambiguous") type.Fields.Add(new InjectedFieldAnalysisContext("other",types.SystemInt32Type,FieldAttributes.Public,type){Offset=0});
        var produce=type.InjectMethodContext("Produce",type,MethodAttributes.Public|MethodAttributes.Static);
        var expected=shape=="whole"?type:shape=="mismatch"?types.SystemSingleType:types.SystemInt32Type;
        var consume=new InjectedMethodAnalysisContext(type,"Consume",types.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static,[expected]);
        var caller=type.InjectMethodContext("Caller",types.SystemVoidType,MethodAttributes.Public|MethodAttributes.Static);
        var storage=new LocalVariable("storage",new Register(null,shape=="nonstack"?"X0":"stack_-A0",1),type);
        var alias=new LocalVariable("alias",new Register(null,"X1",1),type);
        var writer=shape=="notcall"?new Instruction(0,OpCode.Move,storage,new Immediate(0)):new Instruction(0,OpCode.Call,produce,storage);
        var use=new Instruction(2,OpCode.CallVoid,consume,shape=="copied"?alias:storage);
        var middle=shape=="escaped"?new Instruction(1,OpCode.CallVoid,consume,new AddressOf(storage))
            :shape=="fieldwrite"?new Instruction(1,OpCode.Move,new FieldReference(field,storage,0),new Immediate(42))
            :new Instruction(1,OpCode.Move,alias,storage);
        caller.ControlFlowGraph=new([writer,middle,use,new(3,OpCode.Return)]);
        var shouldProject=shape is "exact" or "copied";
        Assert.That(StackFieldZeroRecovery.Run(caller),Is.EqualTo(shouldProject));
        if(shouldProject)
        {
            Assert.That(((FieldReference)use.Operands[1]).Field,Is.SameAs(field));
            Assert.That(StackFieldZeroRecovery.Run(caller),Is.False);
        }
        else Assert.That(use.Operands[1],Is.TypeOf<LocalVariable>());
    }
}
