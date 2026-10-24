using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstructorPrologueRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("write-width-proof", true)]
    [TestCase("integer-local", true)]
    [TestCase("null-local", true)]
    [TestCase("unknown-zero-coverage", false)]
    [TestCase("short-zero-coverage", false)]
    [TestCase("wrong-type", false)]
    [TestCase("unknown-local-type", false)]
    [TestCase("parameter-local", false)]
    [TestCase("duplicate-definition", false)]
    [TestCase("used-by-field-before-base", false)]
    [TestCase("address-escape-before-base", false)]
    [TestCase("callback-before-base", false)]
    [TestCase("memory-read-before-base", false)]
    [TestCase("argument-to-base", false)]
    [TestCase("wrong-parent", false)]
    [TestCase("wrong-receiver", false)]
    [TestCase("virtual-constructor", false)]
    [TestCase("duplicate-base-call", false)]
    [TestCase("not-constructor", false)]
    [TestCase("implicit-clobber", false)]
    [TestCase("exceptional-successor", false)]
    [TestCase("entry-reentry", false)]
    public void OnlyUnobservedProvenLocalInitializersMovePastTheExactBaseCall(string shape, bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var root=app.SystemTypes.SystemObjectType;
        var parent=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","PrologueParent",root,TypeAttributes.Public);
        var owner=new InjectedTypeAnalysisContext(root.DeclaringAssembly,"Test","PrologueChild",parent,TypeAttributes.Public);
        var target=parent.InjectMethodContext(".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public);
        var caller=owner.InjectMethodContext(shape=="not-constructor"?"Caller":".ctor",app.SystemTypes.SystemVoidType,MethodAttributes.Public);
        var valueType=app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="System.Decimal");
        var size=checked((int)TypeSizes.UnboxedSize(valueType,app.Binary.PointerSizeBytes));
        var self=new LocalVariable("this",new(null,"this"),owner){IsThis=true};
        var local=new LocalVariable("local",new(null,"local"),valueType);
        var other=new LocalVariable("other",new(null,"other"),owner);
        var field=owner.InjectFieldContext("Count",app.SystemTypes.SystemInt32Type,FieldAttributes.Private);field.Offset=16;
        var initialize=new Instruction(1,OpCode.Move,local,new DefaultStructValue(valueType)){NativeZeroSize=size};
        var store=new Instruction(2,OpCode.Move,new FieldReference(field,self,16),new Immediate(8)){NativeWriteSize=4};
        var call=new Instruction(3,OpCode.CallVoid,target,self);
        var use=new Instruction(4,OpCode.CallVoid,new StringLiteral("observe_after"),new AddressOf(local));
        var body=new System.Collections.Generic.List<Instruction>{initialize,store,call,use,new(5,OpCode.Return)};
        caller.ParameterLocals=[self];caller.Locals=[self,local,other];
        if(shape=="write-width-proof"){initialize.NativeZeroSize=0;initialize.NativeWriteSize=size;}
        if(shape=="integer-local"){local.Type=app.SystemTypes.SystemInt32Type;initialize.SetOperand(1,new Immediate(7));}
        if(shape=="null-local"){local.Type=root;initialize.SetOperand(1,new Immediate(0));}
        if(shape=="unknown-zero-coverage")initialize.NativeZeroSize=0;
        if(shape=="short-zero-coverage")initialize.NativeZeroSize=size-1;
        if(shape=="wrong-type")local.Type=app.SystemTypes.SystemInt32Type;
        if(shape=="unknown-local-type")local.Type=null;
        if(shape=="parameter-local")caller.ParameterLocals.Add(local);
        if(shape=="duplicate-definition")body.Insert(4,new(6,OpCode.Move,local,new DefaultStructValue(valueType)));
        if(shape=="used-by-field-before-base")store.SetOperand(1,local);
        if(shape=="address-escape-before-base")store.SetOperand(1,new AddressOf(local));
        if(shape=="callback-before-base")body.Insert(2,new(6,OpCode.CallVoid,new StringLiteral("observe_before")));
        if(shape=="memory-read-before-base")body.Insert(2,new(6,OpCode.Move,other,new MemoryOperand(local)));
        if(shape=="argument-to-base")call.AddOperands([local]);
        if(shape=="wrong-parent")owner.BaseType=root;
        if(shape=="wrong-receiver")call.SetOperand(1,other);
        if(shape=="virtual-constructor")call.NativeVirtualDispatch=true;
        if(shape=="duplicate-base-call")body.Insert(4,new(6,OpCode.CallVoid,target,self));
        if(shape=="implicit-clobber")initialize.ImplicitDefinition=new(null,"clobbered");
        caller.ControlFlowGraph=new(body);
        var block=caller.ControlFlowGraph.Blocks.Single(b=>b.Instructions.Contains(call));
        if(shape=="exceptional-successor")
        {block.Successors.Add(caller.ControlFlowGraph.ExitBlock);caller.ControlFlowGraph.ExitBlock.Predecessors.Add(block);}
        if(shape=="entry-reentry")caller.ControlFlowGraph.EntryBlock.Predecessors.Add(block);
        var before=caller.ControlFlowGraph.Instructions.ToArray();
        Assert.That(ConstructorPrologueRecovery.Recover(caller),Is.EqualTo(expected?1:0));
        if(expected)
        {
            Assert.That(block.Instructions.IndexOf(store),Is.LessThan(block.Instructions.IndexOf(call)));
            Assert.That(block.Instructions.IndexOf(initialize),Is.EqualTo(block.Instructions.IndexOf(call)+1));
            Assert.That(ForwardNullCheckRecovery.DefinitionDominates(caller.ControlFlowGraph,initialize,use),Is.True);
            Assert.That(call.Operands[0],Is.SameAs(target));
        }
        else Assert.That(caller.ControlFlowGraph.Instructions,Is.EqualTo(before),"no partial reordering on failed proof");
    }
}
