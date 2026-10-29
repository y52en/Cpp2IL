using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeWord32LoopTests
{
    private ApplicationAnalysisContext _app=null!;
    [OneTimeSetUp]public void Load()=>_app=TestGameLoader.LoadSimple2019Game();
    private static LocalVariable V(string name,TypeAnalysisContext? type=null)=>new(name,new Register(null,name),type);
    private static void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
    private (MethodAnalysisContext Method,LocalVariable Index,LocalVariable Product,Instruction Init,Instruction Update,Instruction Compare,Instruction Multiply,Instruction Address,Block Body) Fixture()
    {
        var method=new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType,"Counter",_app.SystemTypes.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var index=V("counter");var product=V("offset");
        var array=V("array",new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemInt32Type));
        var init=new Instruction(0,OpCode.Move,index,new Immediate(0));
        var compare=new Instruction(1,OpCode.CheckLess,V("condition",_app.SystemTypes.SystemBooleanType),index,V("limit",_app.SystemTypes.SystemInt32Type))
            {NativeComparisonSize=4,UnsignedComparison=true};
        var update=new Instruction(2,OpCode.Add,index,index,new Immediate(1)){NativeArithmeticSize=4};
        var multiply=new Instruction(3,OpCode.Multiply,product,index,new Immediate(120)){NativeArithmeticSize=8,NativeMultiplyInputSize=8};
        var address=new Instruction(4,OpCode.Add,V("address"),array,product){NativeArithmeticSize=8};
        var access=new Instruction(5,OpCode.Move,V("element",_app.SystemTypes.SystemInt32Type),new ArrayAccess(array,index));
        var graph=new ISILControlFlowGraph([]);graph.EntryBlock.Successors.Clear();graph.ExitBlock.Predecessors.Clear();
        var body=new Block{ID=2,Instructions=[init,compare,update,multiply,address,access,new(6,OpCode.Return)]};
        graph.Blocks.Add(body);Edge(graph.EntryBlock,body);Edge(body,graph.ExitBlock);method.ControlFlowGraph=graph;
        return(method,index,product,init,update,compare,multiply,address,body);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AllWordDefinitionsKeepLowBitsAndZeroExtendFullXMultiply(bool signedComparison)
    {
        var f=Fixture();f.Compare.UnsignedComparison=!signedComparison;
        var original=f.Body.Instructions.ToArray();
        Assert.That(NativeWord32LoopRecovery.Run(f.Method),Is.EqualTo(1));
        Assert.That(f.Index.Type,Is.SameAs(_app.SystemTypes.SystemUInt32Type));
        Assert.That(f.Product.Type,Is.SameAs(_app.SystemTypes.SystemUInt64Type));
        Assert.That(f.Compare.UnsignedComparison,Is.EqualTo(!signedComparison));
        Assert.That(f.Body.Instructions,Is.EqualTo(original));
        Assert.That(IlGenerator.NativeIntegerArithmeticType(f.Multiply,f.Method),Is.SameAs(_app.SystemTypes.SystemUInt64Type));
        Assert.That(IlGenerator.IntegralLoadConversion(f.Index,_app.SystemTypes.SystemUInt64Type),
            Is.EqualTo(AsmResolver.PE.DotNet.Cil.CilOpCodes.Conv_U8));
        Assert.That(NativeWord32LoopRecovery.Run(f.Method),Is.Zero);
    }

    [TestCase("unknown-update")]
    [TestCase("wide-update")]
    [TestCase("float-update")]
    [TestCase("unknown-compare")]
    [TestCase("wide-compare")]
    [TestCase("incoming")]
    [TestCase("return-buffer")]
    [TestCase("this")]
    [TestCase("return")]
    [TestCase("method-info")]
    [TestCase("typed")]
    [TestCase("unknown-call")]
    [TestCase("storage-escape")]
    [TestCase("wide-copy")]
    [TestCase("negative-initial")]
    [TestCase("before-initial")]
    [TestCase("other-initial")]
    [TestCase("narrow-multiply")]
    [TestCase("negative-multiplier")]
    [TestCase("typed-product")]
    [TestCase("product-redefined")]
    [TestCase("product-escape")]
    [TestCase("product-use-before-definition")]
    [TestCase("unknown-address-width")]
    public void AnyUnprovedDefinitionOrConsumerRefusesBeforeMutation(string shape)
    {
        var f=Fixture();
        switch(shape)
        {
            case "unknown-update":f.Update.NativeArithmeticSize=0;break;
            case "wide-update":f.Update.NativeArithmeticSize=8;break;
            case "float-update":f.Update.NativeFloatingPointSize=4;break;
            case "unknown-compare":f.Compare.NativeComparisonSize=0;break;
            case "wide-compare":f.Compare.NativeComparisonSize=8;break;
            case "incoming":f.Index.ParameterIndex=0;break;
            case "return-buffer":f.Index.IsReturnBuffer=true;break;
            case "this":f.Index.IsThis=true;break;
            case "return":f.Index.IsReturn=true;break;
            case "method-info":f.Index.IsMethodInfo=true;break;
            case "typed":f.Index.Type=_app.SystemTypes.SystemObjectType;break;
            case "unknown-call":f.Body.Instructions.Add(new(-1,OpCode.CallVoid,new Immediate(123),f.Index));break;
            case "storage-escape":f.Body.Instructions.Add(new(-1,OpCode.Move,V("escaped"),new AddressOf(f.Index)));break;
            case "wide-copy":f.Body.Instructions.Add(new(-1,OpCode.Move,V("copy"),f.Index){NativeRegisterCopySize=8});break;
            case "negative-initial":f.Init.SetOperand(1,new Immediate(-1));break;
            case "before-initial":f.Body.Instructions.Remove(f.Compare);f.Body.Instructions.Insert(0,f.Compare);break;
            case "other-initial":f.Body.Instructions.Insert(1,new(-1,OpCode.Move,f.Index,new Immediate(1)));break;
            case "narrow-multiply":f.Multiply.NativeMultiplyInputSize=4;break;
            case "negative-multiplier":f.Multiply.SetOperand(2,new Immediate(-1));break;
            case "typed-product":f.Product.Type=_app.SystemTypes.SystemObjectType;break;
            case "product-redefined":f.Body.Instructions.Add(new(-1,OpCode.Move,f.Product,new Immediate(0)));break;
            case "product-escape":f.Body.Instructions.Add(new(-1,OpCode.CallVoid,new Immediate(123),f.Product));break;
            case "product-use-before-definition":f.Body.Instructions.Remove(f.Address);f.Body.Instructions.Insert(1,f.Address);break;
            case "unknown-address-width":f.Address.NativeArithmeticSize=0;break;
        }
        var indexType=f.Index.Type;var productType=f.Product.Type;
        Assert.That(NativeWord32LoopRecovery.Run(f.Method),Is.Zero);
        Assert.That(f.Index.Type,Is.SameAs(indexType));
        Assert.That(f.Product.Type,Is.SameAs(productType));
    }
}
