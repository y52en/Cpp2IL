using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NullBypassRuntimeCastRecoveryTests
{
    private static System.Collections.Generic.IEnumerable<TestCaseData> MergeCases()
    {
        foreach(var shape in new[]{"valid","runtime-class-target","null-jump","wrong-helper","wrong-source","wrong-target",
            "wrong-width","wrong-offset","wrong-null-source","wrong-null-polarity","wrong-success-polarity",
            "extra-guard-call","extra-failure-call","extra-transport-call","extra-null-call","wrong-null-value",
            "wrong-null-result","shared-failure","shared-transport","shared-null-path","reassigned-source",
            "extra-result-definition","escaping-flag","escaping-metadata","nested-escaping-metadata","unknown-source",
            "value-target","wrong-copy","wrong-merge-type","merge-parameter","escaping-cast","redefined-cast",
            "array-target","wrong-array-element"})
            yield return new TestCaseData("merge/"+shape,shape is "valid" or "runtime-class-target" or "null-jump" or "array-target" or "shared-null-path");
        foreach(var shape in new[]{"shared-return","shared-return-local","shared-return-nop-before",
            "shared-return-wrong-type","shared-return-unknown-type","shared-return-self-copy","shared-return-missing-copy",
            "shared-return-wrong-destination","shared-return-native-write","shared-return-native-index",
            "shared-return-second-write","shared-return-extra-successor","shared-return-after-copy-call",
            "shared-return-duplicate-edge","shared-return-escaping-flag",
            "shared-return-conditional-to-success","shared-return-conditional-away","shared-return-conditional-bad-flag",
            "shared-return-conditional-bad-target","shared-return-conditional-third-edge"})
            yield return new TestCaseData("merge/"+shape,shape is "shared-return" or "shared-return-local" or "shared-return-nop-before"
                or "shared-return-conditional-to-success" or "shared-return-conditional-away");
    }

    [TestCaseSource(nameof(MergeCases))]
    [TestCase("valid",true)]
    [TestCase("runtime-class-target",true)]
    [TestCase("null-jump",true)]
    [TestCase("wrong-helper",false)]
    [TestCase("wrong-source",false)]
    [TestCase("wrong-target",false)]
    [TestCase("wrong-width",false)]
    [TestCase("wrong-offset",false)]
    [TestCase("wrong-null-source",false)]
    [TestCase("wrong-null-polarity",false)]
    [TestCase("wrong-success-polarity",false)]
    [TestCase("extra-guard-call",false)]
    [TestCase("extra-failure-call",false)]
    [TestCase("extra-transport-call",false)]
    [TestCase("extra-null-call",false)]
    [TestCase("wrong-null-value",false)]
    [TestCase("wrong-null-result",false)]
    [TestCase("shared-failure",false)]
    [TestCase("shared-transport",false)]
    [TestCase("shared-null-path",true)]
    [TestCase("reassigned-source",false)]
    [TestCase("extra-result-definition",false)]
    [TestCase("escaping-flag",false)]
    [TestCase("escaping-metadata",false)]
    [TestCase("nested-escaping-metadata",false)]
    [TestCase("unknown-source",false)]
    [TestCase("value-target",false)]
    public void OnlyCompleteNullBypassAndAutomaticCastFailureIsRewritten(string shape,bool expected)
    {
        var merge=shape.StartsWith("merge/",System.StringComparison.Ordinal);
        if(merge)shape=shape.Substring(6);
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var exceptionType=app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.InvalidCastException");
        LocalVariable Local(string name,TypeAnalysisContext? type=null)=>new(name,new Register(null,name),type);
        var source=Local("source",t.SystemObjectType);var other=Local("other",t.SystemObjectType);
        TypeAnalysisContext target=shape is "array-target" or "wrong-array-element"?new SzArrayTypeAnalysisContext(t.SystemStringType)
            :shape=="value-target"?t.SystemInt32Type:t.SystemStringType;
        var result=Local("result",target);var flag=Local("flag",t.SystemBooleanType);
        var castResult=merge?Local("castResult",target):result;
        var nonnull=Local("nonnull",t.SystemBooleanType);var nullFlag=Local("nullFlag",t.SystemBooleanType);
        var klass=Local("klass");var name=Local("name");var message=Local("message");var exception=Local("exception",exceptionType);
        var graph=new ISILControlFlowGraph([]);
        var before=new Block{ID=20};var guard=new Block{ID=21};var failure=new Block{ID=22};
        var success=new Block{ID=23};var transport=new Block{ID=24};var nullPath=new Block{ID=25};
        graph.Blocks=[graph.EntryBlock,graph.ExitBlock,before,guard,failure,success,transport,nullPath];
        foreach(var block in graph.Blocks){block.Predecessors.Clear();block.Successors.Clear();}
        void Edge(Block a,Block b){a.Successors.Add(b);b.Predecessors.Add(a);}
        Edge(graph.EntryBlock,before);Edge(before,guard);Edge(before,nullPath);
        Edge(guard,failure);Edge(guard,success);Edge(failure,transport);Edge(transport,graph.ExitBlock);
        Edge(nullPath,success);Edge(success,graph.ExitBlock);
        before.Instructions=[new(0,OpCode.CheckEqual,nullFlag,source,new Immediate(0)),new(1,OpCode.ConditionalJump,nullPath,nullFlag)];
        guard.Instructions=[new(2,OpCode.IsInst,castResult,target,source),new(3,OpCode.CheckEqual,flag,castResult,new Immediate(0)),
            new(4,OpCode.Not,nonnull,flag),new(5,OpCode.ConditionalJump,success,nonnull)];
        failure.Instructions=[new(6,OpCode.Move,klass,new MemoryOperand(source)){NativeReadSize=8},
            new(7,OpCode.Move,name,new MemoryOperand(klass,addend:0x40)){NativeReadSize=8},
            new(8,OpCode.Call,new Immediate(0x1234),message,name,target),new(9,OpCode.Newobj,exception,exceptionType)];
        transport.Instructions=[new(10,OpCode.Throw,exception)];
        nullPath.Instructions=[new(11,OpCode.Move,result,new Immediate(0))];
        if(shape=="null-jump")nullPath.Instructions.Add(new(14,OpCode.Jump,success));
        success.Instructions=[new(12,OpCode.Return,result)];
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"Caller",target,MethodAttributes.Public|MethodAttributes.Static,[])
            {ControlFlowGraph=graph,ParameterLocals=[source,other],Locals=[source,other,result,flag,nonnull,nullFlag,klass,name,message,exception]};
        if(shape=="runtime-class-target")failure.Instructions[2].SetOperand(3,new RuntimeClassTypeAnalysisContext(target,t.SystemObjectType.DeclaringAssembly));
        if(shape=="wrong-source")failure.Instructions[0].SetOperand(1,new MemoryOperand(other));
        if(shape=="wrong-target")failure.Instructions[2].SetOperand(3,new RuntimeClassTypeAnalysisContext(t.SystemObjectType,t.SystemObjectType.DeclaringAssembly));
        if(shape=="wrong-width")failure.Instructions[0].NativeReadSize=4;
        if(shape=="wrong-offset")failure.Instructions[1].SetOperand(1,new MemoryOperand(klass,addend:0x48));
        if(shape=="wrong-null-source")before.Instructions[0].SetOperand(1,other);
        if(shape=="wrong-null-polarity")before.Instructions[0].OpCode=OpCode.CheckNotEqual;
        if(shape=="wrong-success-polarity")guard.Instructions[2].OpCode=OpCode.Negate;
        if(shape=="extra-guard-call")guard.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="extra-failure-call")failure.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="extra-transport-call")transport.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="extra-null-call")nullPath.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="wrong-null-value")nullPath.Instructions[0].SetOperand(1,new Immediate(1));
        if(shape=="wrong-null-result")nullPath.Instructions[0].SetOperand(0,other);
        if(shape=="shared-failure")Edge(before,failure);
        if(shape=="shared-transport")Edge(before,transport);
        if(shape=="shared-null-path")Edge(graph.EntryBlock,nullPath);
        if(shape=="reassigned-source")success.Instructions.Insert(0,new(13,OpCode.Move,source,other));
        if(shape=="extra-result-definition")success.Instructions.Insert(0,new(13,OpCode.Move,result,new Immediate(0)));
        if(shape=="escaping-flag")success.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("observe"),flag));
        if(shape=="escaping-metadata")success.Instructions.Insert(0,new(13,OpCode.CallVoid,new StringLiteral("observe"),name));
        if(shape=="nested-escaping-metadata")success.Instructions.Insert(0,new(13,OpCode.Move,other,new MemoryOperand(name)));
        if(shape=="unknown-source")source.Type=null;
        if(merge)
        {
            var copy=new Instruction(-1,OpCode.Move,result,castResult);
            guard.Instructions.Insert(guard.Instructions.Count-1,copy);
            method.Locals.Add(castResult);
            if(shape=="wrong-copy")copy.SetOperand(1,other);
            if(shape=="wrong-merge-type")result.Type=t.SystemObjectType;
            if(shape=="merge-parameter")method.ParameterLocals.Add(result);
            if(shape=="escaping-cast")success.Instructions.Insert(0,new(15,OpCode.CallVoid,new StringLiteral("observe"),castResult));
            if(shape=="redefined-cast")success.Instructions.Insert(0,new(15,OpCode.Move,castResult,new Immediate(0)));
            if(shape is "array-target" or "wrong-array-element")
            {
                result.Type=new SzArrayTypeAnalysisContext(shape=="wrong-array-element"?t.SystemInt32Type:t.SystemStringType);
                failure.Instructions[2].SetOperand(3,new SzArrayTypeAnalysisContext(t.SystemStringType));
            }
        }
        Block? incomingApplicationPath=null;
        if(shape.StartsWith("shared-return",System.StringComparison.Ordinal))
        {
            var incoming=new Block{ID=30};var split=new Block{ID=31};incomingApplicationPath=incoming;
            graph.Blocks.Add(incoming);graph.Blocks.Add(split);
            graph.RemoveEdge(graph.EntryBlock,before);Edge(graph.EntryBlock,split);
            Edge(split,incoming);Edge(split,before);Edge(incoming,success);
            var select=Local("applicationNull",t.SystemBooleanType);method.Locals.Add(select);
            split.Instructions=[new(16,OpCode.CheckEqual,select,source,new Immediate(0)),
                new(17,OpCode.ConditionalJump,incoming,select)];
            IOperand value=new Immediate(0);
            if(shape is "shared-return-local" or "shared-return-wrong-type" or "shared-return-unknown-type")
            {
                var supplied=Local("applicationValue",shape=="shared-return-unknown-type"?null:
                    shape=="shared-return-wrong-type"?t.SystemInt32Type:target);
                method.Locals.Add(supplied);incoming.Instructions.Add(new(18,OpCode.Move,supplied,new Immediate(0)));value=supplied;
            }
            if(shape=="shared-return-self-copy")value=result;
            var applicationCopy=new Instruction(-1,OpCode.Move,result,value);
            incoming.Instructions.Add(applicationCopy);incoming.Instructions.Add(new(19,OpCode.Jump,success));
            if(shape=="shared-return-nop-before")incoming.Instructions.Insert(0,new(20,OpCode.Nop));
            if(shape=="shared-return-missing-copy")incoming.Instructions.Remove(applicationCopy);
            if(shape=="shared-return-wrong-destination")applicationCopy.SetOperand(0,other);
            if(shape=="shared-return-native-write")applicationCopy.NativeWriteSize=8;
            if(shape=="shared-return-native-index")applicationCopy.Index=20;
            if(shape=="shared-return-second-write")incoming.Instructions.Insert(0,new(-1,OpCode.Move,result,new Immediate(0)));
            if(shape.StartsWith("shared-return-conditional",System.StringComparison.Ordinal))
            {
                Edge(incoming,nullPath);
                var branchTarget=shape=="shared-return-conditional-away"?nullPath:success;
                incoming.Instructions[^1]=new(19,OpCode.ConditionalJump,branchTarget,select);
                if(shape=="shared-return-conditional-bad-flag")incoming.Instructions[^1].SetOperand(1,Local("notBoolean",t.SystemInt32Type));
                if(shape=="shared-return-conditional-bad-target")incoming.Instructions[^1].SetOperand(0,transport);
                if(shape=="shared-return-conditional-third-edge")Edge(incoming,transport);
            }
            if(shape=="shared-return-extra-successor")Edge(incoming,nullPath);
            if(shape=="shared-return-after-copy-call")incoming.Instructions.Insert(incoming.Instructions.Count-1,new(20,OpCode.CallVoid,new StringLiteral("callback")));
            if(shape=="shared-return-duplicate-edge")Edge(incoming,success);
            if(shape=="shared-return-escaping-flag")incoming.Instructions.Insert(0,new(20,OpCode.CallVoid,new StringLiteral("observe"),flag));
        }
        var applicationInstructions=incomingApplicationPath?.Instructions.ToArray();
        var originalContinuation=success.Instructions.ToArray();
        foreach(var block in graph.Blocks)block.CalculateBlockType();
        var originals=graph.Instructions.ToArray();
        var originalNullInstructions=nullPath.Instructions.ToArray();
        var originalNullPredecessors=nullPath.Predecessors.ToArray();
        Assert.That(NullBypassRuntimeCastRecovery.TryRecover(method,guard,a=>a==0x1234 && shape!="wrong-helper"),Is.EqualTo(expected));
        if(!expected)Assert.That(graph.Instructions,Is.EqualTo(originals));
        else
        {
            Assert.That(success.Instructions,Is.EqualTo(originalContinuation));
            if(incomingApplicationPath!=null)Assert.That(incomingApplicationPath.Instructions,Is.EqualTo(applicationInstructions));
            Assert.That(nullPath.Instructions,Is.EqualTo(originalNullInstructions));
            Assert.That(nullPath.Predecessors,Is.EqualTo(originalNullPredecessors));
            Assert.That(guard.Instructions[0].OpCode,Is.EqualTo(OpCode.CastClass));
            Assert.That(guard.Instructions.Last().Operands[0],Is.SameAs(success));
            Assert.That(before.Instructions.Last().Operands[0],Is.SameAs(nullPath));
            Assert.That(nullPath.Instructions[0].Operands[0],Is.SameAs(result));
            Assert.That(((Immediate)nullPath.Instructions[0].Operands[1]).Value,Is.Zero);
            ExecuteNewFixture(graph,source);
        }
    }

    [TestCase(GenericParameterAttributes.None,false)]
    [TestCase(GenericParameterAttributes.ReferenceTypeConstraint,true)]
    [TestCase(GenericParameterAttributes.NotNullableValueTypeConstraint,false)]
    [TestCase(GenericParameterAttributes.ReferenceTypeConstraint|GenericParameterAttributes.NotNullableValueTypeConstraint,false)]
    public void GenericReferenceProofNeverComesFromSharedObjectAlias(GenericParameterAttributes attributes,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var owner=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Test","GenericOwner",t.SystemObjectType,TypeAttributes.Public);
        var parameter=new GenericParameterTypeAnalysisContext("T",0,LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,attributes,owner);
        Assert.That(NullBypassRuntimeCastRecovery.ReferenceType(parameter),Is.EqualTo(expected));
        if(attributes==GenericParameterAttributes.None)
        {
            parameter.ConstraintTypes.Add(t.SystemObjectType);
            Assert.That(NullBypassRuntimeCastRecovery.ReferenceType(parameter),Is.False,"System.Object does not exclude value types");
            parameter.ConstraintTypes.Add(app.Assemblies.SelectMany(a=>a.Types).Single(x=>x.FullName=="System.Exception"));
            Assert.That(NullBypassRuntimeCastRecovery.ReferenceType(parameter),Is.True);
        }
    }

    private static void ExecuteNewFixture(ISILControlFlowGraph graph,LocalVariable source)
    {
        // Execute only newly emitted fixture IL, never any original game DLL.
        var dynamic=new System.Reflection.Emit.DynamicMethod("NullBypassFixture",typeof(object),[typeof(object)]);
        var il=dynamic.GetILGenerator();
        var target=graph.Instructions.First(i=>i.OpCode==OpCode.CastClass).Operands[1] is TypeAnalysisContext {FullName:"System.String[]"}
            ?typeof(string[]):typeof(string);
        var labels=graph.Blocks.ToDictionary(b=>b,_=>il.DefineLabel());
        var locals=new System.Collections.Generic.Dictionary<LocalVariable,System.Reflection.Emit.LocalBuilder>();
        System.Reflection.Emit.LocalBuilder Local(LocalVariable value)
        {
            if(!locals.TryGetValue(value,out var local))
                locals[value]=local=il.DeclareLocal(value.Type?.FullName=="System.Boolean"?typeof(bool):typeof(object));
            return local;
        }
        void Load(IOperand operand)
        {
            if(ReferenceEquals(operand,source))il.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
            else if(operand is LocalVariable local)il.Emit(System.Reflection.Emit.OpCodes.Ldloc,Local(local));
            else if(operand is Immediate {Value:0})il.Emit(System.Reflection.Emit.OpCodes.Ldnull);
            else throw new System.Exception("unsupported fixture operand");
        }
        var reachable=new System.Collections.Generic.HashSet<Block>();
        var pending=new System.Collections.Generic.Queue<Block>();pending.Enqueue(graph.EntryBlock);
        while(pending.Count>0)
        {
            var block=pending.Dequeue();if(!reachable.Add(block))continue;
            foreach(var successor in block.Successors)pending.Enqueue(successor);
        }
        foreach(var block in graph.Blocks.Where(b=>reachable.Contains(b) && !ReferenceEquals(b,graph.ExitBlock)))
        {
            il.MarkLabel(labels[block]);
            foreach(var instruction in block.Instructions)
            {
                switch(instruction.OpCode)
                {
                    case OpCode.Nop:break;
                    case OpCode.Move:
                        Load(instruction.Operands[1]);il.Emit(System.Reflection.Emit.OpCodes.Stloc,Local((LocalVariable)instruction.Operands[0]));break;
                    case OpCode.CheckEqual:
                        Load(instruction.Operands[1]);Load(instruction.Operands[2]);il.Emit(System.Reflection.Emit.OpCodes.Ceq);
                        il.Emit(System.Reflection.Emit.OpCodes.Stloc,Local((LocalVariable)instruction.Operands[0]));break;
                    case OpCode.CastClass:
                        Load(instruction.Operands[2]);il.Emit(System.Reflection.Emit.OpCodes.Castclass,target);
                        il.Emit(System.Reflection.Emit.OpCodes.Stloc,Local((LocalVariable)instruction.Operands[0]));break;
                    case OpCode.Jump:il.Emit(System.Reflection.Emit.OpCodes.Br,labels[(Block)instruction.Operands[0]]);break;
                    case OpCode.ConditionalJump:
                        Load(instruction.Operands[1]);il.Emit(System.Reflection.Emit.OpCodes.Brtrue,labels[(Block)instruction.Operands[0]]);break;
                    case OpCode.Return:Load(instruction.Operands[0]);il.Emit(System.Reflection.Emit.OpCodes.Ret);break;
                    default:throw new System.Exception("unsupported reachable fixture instruction");
                }
            }
            var last=block.Instructions.LastOrDefault();
            if(last?.OpCode==OpCode.ConditionalJump)
                il.Emit(System.Reflection.Emit.OpCodes.Br,labels[block.Successors.Single(b=>!ReferenceEquals(b,last.Operands[0]))]);
            else if(last?.OpCode is not (OpCode.Jump or OpCode.Return) && block.Successors.Count==1)
                il.Emit(System.Reflection.Emit.OpCodes.Br,labels[block.Successors[0]]);
        }
        var run=(System.Func<object?,object?>)dynamic.CreateDelegate(typeof(System.Func<object?,object?>));
        Assert.That(run(null),Is.Null);
        object valid=target==typeof(string[])?new[]{"fixture"}:"fixture";
        Assert.That(run(valid),Is.SameAs(valid));
        Assert.Throws<System.InvalidCastException>(()=>run(new object()));
    }
}
