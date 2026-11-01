using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CovariantArrayStoreRecoveryTests
{
    [TestCase("valid", true)]
    [TestCase("late-array-class", true)]
    [TestCase("late-array-class-wrong-offset", false)]
    [TestCase("late-array-class-multiple-definitions", false)]
    [TestCase("wrong-class-type", false)]
    [TestCase("unknown-array-type", false)]
    [TestCase("callback", false)]
    [TestCase("wrong-array", false)]
    [TestCase("wrong-value", false)]
    [TestCase("wrong-offset", false)]
    [TestCase("escaping-result", false)]
    [TestCase("nested-escaping-result", false)]
    [TestCase("alias-escaping-result", false)]
    [TestCase("escaping-predicate", false)]
    [TestCase("shared-failure", false)]
    [TestCase("custom-throw", false)]
    [TestCase("wrong-helper", false)]
    [TestCase("value-element", false)]
    [TestCase("with-bounds", true)]
    [TestCase("wrong-bounds-array", false)]
    [TestCase("wrong-bounds-index", false)]
    [TestCase("string-literal", true)]
    [TestCase("reference-field", true)]
    [TestCase("scalar-field", false)]
    [TestCase("unknown-memory", false)]
    [TestCase("equivalent-reference-field", true)]
    [TestCase("equivalent-string-literal", true)]
    [TestCase("with-zero-bounds", true)]
    [TestCase("wrong-zero-bounds-index", false)]
    [TestCase("compound-bounds", true)]
    [TestCase("compound-bounds-swapped", true)]
    [TestCase("compound-bounds-wrong-array", false)]
    [TestCase("compound-bounds-wrong-index", false)]
    [TestCase("compound-bounds-wrong-constant", false)]
    [TestCase("compound-bounds-wrong-lower", false)]
    [TestCase("compound-bounds-wrong-unequal", false)]
    [TestCase("compound-bounds-negative", false)]
    [TestCase("element-snapshot", true)]
    [TestCase("element-snapshot-wrong-width", false)]
    [TestCase("element-snapshot-redefined", false)]
    [TestCase("element-snapshot-late", false)]
    [TestCase("element-snapshot-escaped", false)]
    [TestCase("with-zero-bounds-snapshot", true)]
    [TestCase("compound-bounds-snapshot", true)]
    [TestCase("compound-bounds-snapshot-wrong-width", false)]
    [TestCase("compound-bounds-snapshot-redefined", false)]
    [TestCase("compound-bounds-snapshot-wrong-array", false)]
    public void OnlyAProvenFollowingReferenceArrayStoreSuppliesTheCheck(string shape, bool expected)
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var types = app.SystemTypes;
        var arrayType = new SzArrayTypeAnalysisContext(shape == "value-element" ? types.SystemInt32Type : types.SystemObjectType);
        var array = new LocalVariable("array", new Register(null, "array"), arrayType);
        var otherArray = new LocalVariable("other", new Register(null, "other"), arrayType);
        var klass = new LocalVariable("klass", new Register(null, "klass"), new RuntimeClassTypeAnalysisContext(arrayType, arrayType.DeclaringAssembly));
        if (shape.StartsWith("late-array-class", StringComparison.Ordinal)) klass.Type = null;
        if (shape == "wrong-class-type") klass.Type = types.SystemObjectType;
        if (shape == "unknown-array-type") { klass.Type = null; array.Type = null; }
        var value = new LocalVariable("value", new Register(null, "value"), types.SystemObjectType);
        var result = new LocalVariable("result", new Register(null, "result"), types.SystemObjectType);
        var flag = new LocalVariable("flag", new Register(null, "flag"), types.SystemBooleanType);
        var exceptionType = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.ArrayTypeMismatchException");
        var exception = new LocalVariable("exception", new Register(null, "exception"), exceptionType);
        var method = new InjectedMethodAnalysisContext(types.SystemObjectType, "Caller", types.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var cfg = new ISILControlFlowGraph([]); method.ControlFlowGraph = cfg;
        method.Locals = [array, otherArray, klass, value, result, flag, exception];
        method.ParameterLocals = [array, value]; method.AnalysisWarnings = [];
        IOperand storedValue=value;
        if(shape is "string-literal" or "equivalent-string-literal")storedValue=new StringLiteral("test reference value");
        if(shape is "reference-field" or "equivalent-reference-field" or "scalar-field")
        {
            var holder=new InjectedTypeAnalysisContext(types.SystemObjectType.DeclaringAssembly,"Test","Holder",types.SystemObjectType,TypeAttributes.Public);
            var field=holder.InjectFieldContext("value",shape=="scalar-field"?types.SystemInt32Type:types.SystemStringType,FieldAttributes.Public);
            var receiver=new LocalVariable("holder",new Register(null,"holder"),holder);
            storedValue=new FieldReference(field,receiver,16);
        }
        if(shape=="unknown-memory")storedValue=new MemoryOperand(value,addend:16);
        var guard = new Block { ID = 2 }; var store = new Block { ID = 3 }; var fail = new Block { ID = 4 };
        cfg.Blocks.AddRange([guard, store, fail]);
        void Edge(Block from, Block to) { from.Successors.Add(to); to.Predecessors.Add(from); }
        Edge(cfg.EntryBlock, guard); Edge(guard, store); Edge(guard, fail); Edge(store, cfg.ExitBlock); Edge(fail, cfg.ExitBlock);
        var call = new Instruction(1, OpCode.Call, new StringLiteral(shape == "wrong-helper" ? "unknown" : "il2cpp_vm_object_is_inst"), result, storedValue,
            new MemoryOperand(klass, addend: shape == "wrong-offset" ? 0x48 : 0x40));
        guard.Instructions = [new(0, OpCode.Move, klass, new MemoryOperand(array)), call,
            new(2, OpCode.CheckNotEqual, flag, result, new Immediate(0)), new(3, OpCode.ConditionalJump, store, flag)];
        if (shape == "late-array-class-wrong-offset") guard.Instructions[0].SetOperand(1, new MemoryOperand(array, addend: 8));
        if (shape == "late-array-class-multiple-definitions") guard.Instructions.Insert(1, new(100, OpCode.Move, klass, new MemoryOperand(otherArray)));
        if(shape.StartsWith("element-snapshot",StringComparison.Ordinal))
        {
            var element=new LocalVariable("element",new Register(null,"element"));
            var load=new Instruction(200,OpCode.Move,element,new MemoryOperand(klass,addend:0x40))
                {NativeReadSize=shape=="element-snapshot-wrong-width"?4:8};
            guard.Instructions.Insert(shape=="element-snapshot-late"?2:1,load);
            call.SetOperand(3,element);
            if(shape=="element-snapshot-redefined")guard.Instructions.Insert(2,new(201,OpCode.Move,element,new Immediate(0)));
            if(shape=="element-snapshot-escaped")guard.Instructions.Insert(2,new(201,OpCode.Move,value,new AddressOf(element)));
        }
        var write = new Instruction(4, OpCode.Move, new ArrayAccess(shape == "wrong-array" ? otherArray : array, new Immediate(0)),
            shape == "wrong-value" ? new Immediate(0) : storedValue);
        if(shape=="equivalent-reference-field" && storedValue is FieldReference sourceField)
            write.SetOperand(1,new FieldReference(sourceField.Field,sourceField.Local,sourceField.Offset));
        if(shape=="equivalent-string-literal")write.SetOperand(1,new StringLiteral("test reference value"));
        store.Instructions = [write, new(5, OpCode.Return)];
        fail.Instructions = [new(6, OpCode.Newobj, exception, exceptionType), new(7, OpCode.Throw, exception)];
        if (shape == "callback") store.Instructions.Insert(0, new(8, OpCode.CallVoid, new StringLiteral("callback")));
        if (shape == "escaping-result") store.Instructions.Insert(1, new(9, OpCode.CallVoid, new StringLiteral("observe"), result));
        if (shape == "escaping-predicate") store.Instructions.Insert(1, new(9, OpCode.CallVoid, new StringLiteral("observe"), flag));
        if (shape == "nested-escaping-result") store.Instructions.Insert(1, new(9, OpCode.Move, value, new MemoryOperand(result)));
        if (shape == "alias-escaping-result")
        {
            var alias = new LocalVariable("alias", new Register(null, "alias"), types.SystemObjectType);
            guard.Instructions.Insert(2, new(15, OpCode.Move, alias, result));
            store.Instructions.Insert(1, new(16, OpCode.CallVoid, new StringLiteral("observe"), alias));
        }
        if (shape == "shared-failure") Edge(cfg.EntryBlock, fail);
        if (shape == "custom-throw") fail.Instructions.Insert(0, new(10, OpCode.CallVoid, new StringLiteral("log")));
        if (shape.Contains("bounds"))
        {
            var bounds = new Block { ID = 5 }; var outOfRange = new Block { ID = 6 };
            cfg.Blocks.AddRange([bounds, outOfRange]); cfg.RemoveEdge(guard, store);
            Edge(guard, bounds); Edge(bounds, store); Edge(bounds, outOfRange); Edge(outOfRange, cfg.ExitBlock);
            guard.Instructions.Last().SetOperand(0, bounds);
            var index = new LocalVariable("index", new Register(null, "index"), types.SystemInt32Type);
            var inBounds = new LocalVariable("inBounds", new Register(null, "inBounds"), types.SystemBooleanType);
            bounds.Instructions = [new(11, OpCode.CheckLess, inBounds, index, new ArrayLength(shape == "wrong-bounds-array" ? otherArray : array)),
                new(12, OpCode.ConditionalJump, store, inBounds)];
            write.SetOperand(0, new ArrayAccess(array, shape == "wrong-bounds-index" ? new Immediate(0) : index));
            if(shape.Contains("zero-bounds"))
            {
                bounds.Instructions=[new(11,OpCode.CheckNotEqual,inBounds,new ArrayLength(array),new Immediate(0)),
                    new(12,OpCode.ConditionalJump,store,inBounds)];
                write.SetOperand(0,new ArrayAccess(array,new Immediate(shape=="wrong-zero-bounds-index"?1:0)));
            }
            if(shape.StartsWith("compound-bounds",StringComparison.Ordinal))
            {
                var borrow=new LocalVariable("borrow",new Register(null,"borrow"),types.SystemBooleanType);
                var noBorrow=new LocalVariable("noBorrow",new Register(null,"noBorrow"),types.SystemBooleanType);
                var difference=new LocalVariable("difference",new Register(null,"difference"),types.SystemInt32Type);
                var equal=new LocalVariable("equal",new Register(null,"equal"),types.SystemBooleanType);
                var unequal=new LocalVariable("unequal",new Register(null,"unequal"),types.SystemBooleanType);
                var constant=shape=="compound-bounds-negative"?-1:1;
                bounds.Instructions=[
                    new(20,OpCode.CheckLess,borrow,new ArrayLength(array),new Immediate(constant)),
                    new(21,OpCode.Not,noBorrow,borrow),
                    new(22,OpCode.Subtract,difference,new ArrayLength(shape=="compound-bounds-wrong-array"?otherArray:array),
                        new Immediate(shape=="compound-bounds-wrong-constant"?2:constant)),
                    new(23,OpCode.CheckEqual,equal,difference,new Immediate(0)),
                    new(24,OpCode.Not,unequal,equal),
                    new(25,OpCode.And,inBounds,
                        shape=="compound-bounds-swapped"?unequal:shape=="compound-bounds-wrong-lower"?borrow:noBorrow,
                        shape=="compound-bounds-swapped"?noBorrow:shape=="compound-bounds-wrong-unequal"?equal:unequal),
                    new(26,OpCode.ConditionalJump,store,inBounds)];
                write.SetOperand(0,new ArrayAccess(array,new Immediate(shape=="compound-bounds-wrong-index"?2:constant)));
            }
            var outOfRangeType = app.Assemblies.SelectMany(a => a.Types).Single(t => t.FullName == "System.IndexOutOfRangeException");
            if(shape.Contains("bounds-snapshot",StringComparison.Ordinal))
            {
                var lengthSnapshot=new LocalVariable("lengthSnapshot",new Register(null,"lengthSnapshot"),types.SystemInt32Type);
                foreach(var instruction in bounds.Instructions)
                for(var slot=1;slot<instruction.Operands.Count;slot++)
                    if(instruction.Operands[slot] is ArrayLength)instruction.SetOperand(slot,lengthSnapshot);
                bounds.Instructions.Insert(0,new Instruction(210,OpCode.Move,lengthSnapshot,
                    new ArrayLength(shape=="compound-bounds-snapshot-wrong-array"?otherArray:array))
                    {NativeReadSize=shape=="compound-bounds-snapshot-wrong-width"?8:4});
                if(shape=="compound-bounds-snapshot-redefined")
                    bounds.Instructions.Insert(1,new(211,OpCode.Move,lengthSnapshot,new Immediate(2)));
            }
            var boundsException = new LocalVariable("boundsException", new Register(null, "boundsException"), outOfRangeType);
            outOfRange.Instructions = [new(13, OpCode.Newobj, boundsException, outOfRangeType), new(14, OpCode.Throw, boundsException)];
        }
        foreach (var block in cfg.Blocks) block.CalculateBlockType();
        Assert.That(CovariantArrayStoreRecovery.TryRecover(method, guard), Is.EqualTo(expected));
        Assert.That(call.OpCode == OpCode.Nop, Is.EqualTo(expected));
        Assert.That(store.Instructions.Contains(write), Is.True);
        Assert.That(guard.Successors.Contains(fail), Is.EqualTo(!expected));
    }
}
