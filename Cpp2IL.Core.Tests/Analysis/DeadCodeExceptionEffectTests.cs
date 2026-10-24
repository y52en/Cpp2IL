using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DeadCodeExceptionEffectTests
{
    [TestCase("length")]
    [TestCase("element")]
    [TestCase("field")]
    [TestCase("static-field")]
    [TestCase("static-field-metadata-storage")]
    [TestCase("divide")]
    [TestCase("modulo")]
    public void UnusedResultDoesNotEraseManagedReadOrArithmeticException(string shape)
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var owner=new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,"Fixture","Observed",
            app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),
            shape=="static-field-metadata-storage"?new RuntimeClassTypeAnalysisContext(owner,owner.DeclaringAssembly):owner);
        var array=new LocalVariable("array",new Register(null,"array"),new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var dead=new LocalVariable("unused",new Register(null,"unused"),app.SystemTypes.SystemInt32Type);
        var field=owner.InjectFieldContext("Value",app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public|(shape.StartsWith("static-field")?FieldAttributes.Static:0));
        IOperand source=shape switch {
            "length"=>new ArrayLength(array),"element"=>new ArrayAccess(array,new Immediate(0)),
            _=>new FieldReference(field,receiver,16)};
        var operation=shape is "divide" or "modulo"
            ?new Instruction(0,shape=="divide"?OpCode.Divide:OpCode.Modulo,dead,new Immediate(1),new Immediate(0))
            :new Instruction(0,OpCode.Move,dead,source);
        var graph=new ISILControlFlowGraph([operation,new Instruction(1,OpCode.Return)]);
        DeadCodeEliminator.Run(graph);
        Assert.That(operation.OpCode,Is.Not.EqualTo(OpCode.Nop));
    }

    [Test]
    public void SideEffectingArrayGuardSurvivesEvenWithNoResultConsumer()
    {
        var app=TestGameLoader.LoadSimple2019Game();
        var array=new LocalVariable("array",new Register(null,"array"),new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var guard=new Instruction(0,OpCode.ArrayNullCheck,array);
        var graph=new ISILControlFlowGraph([guard,new Instruction(1,OpCode.Return)]);
        DeadCodeEliminator.Run(graph);Assert.That(guard.OpCode,Is.EqualTo(OpCode.ArrayNullCheck));
    }
}
