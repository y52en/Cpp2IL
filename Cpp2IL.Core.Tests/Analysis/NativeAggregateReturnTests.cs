using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeAggregateReturnTests
{
    private ApplicationAnalysisContext _app=null!;
    private TypeAnalysisContext _value=null!;
    private long _size;

    [OneTimeSetUp]
    public void Load()
    {
        _app=TestGameLoader.LoadSimple2019Game();
        _value=_app.Assemblies.SelectMany(a=>a.Types).Single(t=>t.FullName=="UnityEngine.Matrix4x4");
        _size=TypeSizes.UnboxedSize(_value,8);
        Assert.That(_size,Is.EqualTo(64));
    }

    private LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new Register(null,name),type);
    private static void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}

    private (MethodAnalysisContext Method,Instruction Call,Instruction Return,LocalVariable Destination,LocalVariable Result) Fixture(bool zero=false)
    {
        var method=new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType,"Caller",_value,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var register=_app.InstructionSet.CallingConventionResolver!.HiddenReturnBufferRegister(method);
        Assert.That(register,Is.Not.Null);
        var destination=new LocalVariable("not-a-special-name",register!.Value,_value){IsReturnBuffer=true};
        var result=Local("returned",_value);result.IsReturn=true;
        var source=zero?(IOperand)new Immediate(0):new AddressOf(Local("source",_value));
        var call=new Instruction(0,OpCode.Call,new Immediate(zero?0xA5FF10:0xA5FC30),result,destination,source,new Immediate(_size));
        var returned=new Instruction(1,OpCode.Return,result);
        // The production pass runs after CFG simplification has merged the
        // call's fallthrough and its return into one block.
        var graph=new ISILControlFlowGraph([]);
        graph.EntryBlock.Successors.Clear();graph.ExitBlock.Predecessors.Clear();
        var body=new Block{ID=2,Instructions=[call,returned]};graph.Blocks.Add(body);
        Edge(graph.EntryBlock,body);Edge(body,graph.ExitBlock);
        method.ControlFlowGraph=graph;
        return(method,call,returned,destination,result);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void CompleteTypedCopyOrZeroReturnBecomesAValueMove(bool zero)
    {
        var f=Fixture(zero);
        Assert.That(NativeAggregateReturnRecovery.TryRewrite(f.Method,f.Call,true),Is.True);
        Assert.That(f.Call.OpCode,Is.EqualTo(OpCode.Move));
        Assert.That(f.Call.Operands[0],Is.SameAs(f.Result));
        if(zero)Assert.That(f.Call.Operands[1],Is.TypeOf<DefaultStructValue>());
        else Assert.That(f.Call.Operands[1],Is.TypeOf<LocalVariable>());
        Assert.That(f.Return.Operands[0],Is.SameAs(f.Result));
        Assert.That(NativeAggregateReturnRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
    }

    [TestCase("unreviewed")]
    [TestCase("hidden-flag")]
    [TestCase("wrong-size")]
    [TestCase("larger-size")]
    [TestCase("wrong-import")]
    [TestCase("virtual")]
    [TestCase("scalar")]
    [TestCase("wrong-source")]
    [TestCase("extra-reference")]
    [TestCase("used-result")]
    [TestCase("redefined-result")]
    [TestCase("not-tail")]
    [TestCase("indirect-jump")]
    public void NoUnprovenOperationIsSilentlyRemoved(string shape)
    {
        var f=Fixture();var graph=f.Method.ControlFlowGraph!;
        var block=graph.Blocks.Single(b=>b.Instructions.Contains(f.Call));
        switch(shape)
        {
            case "hidden-flag":f.Destination.IsReturnBuffer=false;break;
            case "wrong-size":f.Call.SetOperand(4,new Immediate(_size-4));break;
            case "larger-size":f.Call.SetOperand(4,new Immediate(_size+4));break;
            case "wrong-import":f.Call.SetOperand(0,new Immediate(0xA5FC34));break;
            case "virtual":f.Call.NativeVirtualDispatch=true;break;
            case "scalar":f.Method.ReturnType=_app.SystemTypes.SystemInt32Type;break;
            case "wrong-source":f.Call.SetOperand(3,new AddressOf(Local("wrong",_app.SystemTypes.SystemObjectType)));break;
            case "extra-reference":f.Call.SetOperands([..f.Call.Operands,new AddressOf(f.Destination)]);break;
            case "used-result":block.Instructions.Insert(0,new(-1,OpCode.CallVoid,new Immediate(123),f.Result));break;
            case "redefined-result":block.Instructions.Insert(0,new(-1,OpCode.Move,f.Result,new DefaultStructValue(_value)));break;
            case "not-tail":block.Instructions.Insert(1,new(-1,OpCode.CallVoid,new Immediate(123)));break;
            case "indirect-jump":block.Instructions.Insert(0,new(-1,OpCode.IndirectJump,new Immediate(123)));break;
        }
        var operands=f.Call.Operands.ToArray();var opcode=f.Call.OpCode;
        Assert.That(NativeAggregateReturnRecovery.TryRewrite(f.Method,f.Call,shape!="unreviewed"),Is.False);
        Assert.That(f.Call.OpCode,Is.EqualTo(opcode));Assert.That(f.Call.Operands,Is.EqualTo(operands));
    }

    [Test]
    public void NonzeroMemsetIsNotDefaultInitialization()
    {
        var f=Fixture(true);f.Call.SetOperand(3,new Immediate(1));
        Assert.That(NativeAggregateReturnRecovery.TryRewrite(f.Method,f.Call,true),Is.False);
    }

    [TestCase("valid",true)]
    [TestCase("inverted",true)]
    [TestCase("length-is-null-check",true)]
    [TestCase("no-length-dereference",false)]
    [TestCase("clobber-array-before-branch",false)]
    [TestCase("clobber-index-before-branch",false)]
    [TestCase("clobber-length-before-branch",false)]
    [TestCase("signed",false)]
    [TestCase("wrong-index",false)]
    [TestCase("wrong-array",false)]
    [TestCase("clobber-index",false)]
    [TestCase("clobber-array",false)]
    [TestCase("escaped-index",false)]
    [TestCase("wrong-success",false)]
    [TestCase("unchecked-entry",false)]
    public void ArrayCopyRequiresActualDominatingStableUnsignedBoundsAndNullChecks(string shape,bool expected)
    {
        var f=Fixture();var graph=new ISILControlFlowGraph([]);f.Method.ControlFlowGraph=graph;
        graph.EntryBlock.Successors.Clear();graph.ExitBlock.Predecessors.Clear();
        var guard=new Block{ID=2};var success=new Block{ID=3};var failure=new Block{ID=4};
        graph.Blocks.AddRange([guard,success,failure]);Edge(graph.EntryBlock,guard);
        Edge(guard,success);Edge(guard,failure);Edge(success,graph.ExitBlock);Edge(failure,graph.ExitBlock);
        if(shape=="unchecked-entry")Edge(graph.EntryBlock,success);
        var arrayType=new SzArrayTypeAnalysisContext(_value);
        var array=Local("array",arrayType);var index=Local("index",_app.SystemTypes.SystemInt32Type);
        var length=Local("length",_app.SystemTypes.SystemInt32Type);var flag=Local("flag",_app.SystemTypes.SystemBooleanType);
        var otherArray=Local("otherArray",arrayType);var otherIndex=Local("otherIndex",_app.SystemTypes.SystemInt32Type);
        f.Call.SetOperand(3,new AddressOf(new ArrayAccess(array,index)));
        guard.Instructions=[new(0,OpCode.ArrayNullCheck,array),new(1,OpCode.Move,length,new ArrayLength(shape=="wrong-array"?otherArray:array)),
            new(2,OpCode.CheckLess,flag,shape=="wrong-index"?otherIndex:index,length){UnsignedComparison=shape!="signed"}];
        IOperand condition=flag;
        if(shape=="inverted")
        {
            var inverted=Local("inverted",_app.SystemTypes.SystemBooleanType);
            guard.Instructions.Add(new(3,OpCode.Not,inverted,flag));condition=inverted;
        }
        guard.Instructions.Add(new(4,OpCode.ConditionalJump,shape is "inverted" or "wrong-success"?failure:success,condition));
        if(shape=="length-is-null-check")guard.Instructions.RemoveAt(0);
        if(shape=="no-length-dereference")guard.Instructions[1].SetOperand(1,new Immediate(8));
        if(shape=="clobber-array-before-branch")guard.Instructions.Insert(2,new(-1,OpCode.Move,array,otherArray));
        if(shape=="clobber-index-before-branch")guard.Instructions.Insert(2,new(-1,OpCode.Move,index,new Immediate(0)));
        if(shape=="clobber-length-before-branch")guard.Instructions.Insert(2,new(-1,OpCode.Move,length,new Immediate(0)));
        if(shape=="escaped-index")guard.Instructions.Insert(0,new(-1,OpCode.CallVoid,new Immediate(123),new AddressOf(index)));
        success.Instructions=[f.Call,f.Return];failure.Instructions=[new(8,OpCode.Return,new DefaultStructValue(_value))];
        if(shape=="clobber-index")success.Instructions.Insert(0,new(5,OpCode.Move,index,new Immediate(0)));
        if(shape=="clobber-array")success.Instructions.Insert(0,new(5,OpCode.Move,array,otherArray));
        Assert.That(NativeAggregateReturnRecovery.TryRewrite(f.Method,f.Call,true),Is.EqualTo(expected));
        Assert.That(f.Call.OpCode,Is.EqualTo(expected?OpCode.Move:OpCode.Call));
        Assert.That(guard.Instructions.Last().OpCode,Is.EqualTo(OpCode.ConditionalJump));
    }

    [TestCase("valid",true)]
    [TestCase("stride",false)]
    [TestCase("header",false)]
    [TestCase("narrow-pointer",false)]
    [TestCase("unknown-index",false)]
    public void RawArrayPointerRequiresFullExactElementAndFullWidthAddress(string shape,bool expected)
    {
        var array=Local("array",new SzArrayTypeAnalysisContext(_value));
        var index=Local("index",shape=="unknown-index"?null:_app.SystemTypes.SystemInt32Type);
        var scaled=Local("scaled");var basis=Local("basis");var pointer=Local("pointer");
        var multiply=new Instruction(0,OpCode.Multiply,scaled,index,new Immediate(shape=="stride"?_size+4:_size))
            {NativeArithmeticSize=shape=="narrow-pointer"?4:8};
        var add=new Instruction(1,OpCode.Add,basis,array,scaled){NativeArithmeticSize=8};
        var final=new Instruction(2,OpCode.Add,pointer,basis,new Immediate(shape=="header"?36:32)){NativeArithmeticSize=8};
        var defs=new Dictionary<LocalVariable,Instruction?>{{scaled,multiply},{basis,add},{pointer,final}};
        var result=ArrayRecovery.MatchFullStructPointer(pointer,_value,8,defs);
        Assert.That(result!=null,Is.EqualTo(expected));
        if(expected){Assert.That(result!.Array,Is.SameAs(array));Assert.That(result.Index,Is.SameAs(index));}
    }
}
