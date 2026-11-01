using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Reflection.Emit;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using OpCode=Cpp2IL.Core.ISIL.OpCode;

namespace Cpp2IL.Core.Tests.Analysis;

public class ParameterizedBaseFieldConstructorRecoveryTests
{
    static LocalVariable Local(string n,TypeAnalysisContext type)=>new(n,new Register(null,n),type);

    [TestCase("valid",true)]
    [TestCase("raw-stores",true)]
    [TestCase("base-constant",true)]
    [TestCase("wrong-base-constant",false)]
    [TestCase("shared-base-field-argument",true)]
    [TestCase("shared-base-field-conflict",false)]
    [TestCase("missing-base-argument",false)]
    [TestCase("extra-base-argument",false)]
    [TestCase("wrong-base-owner",false)]
    [TestCase("late-base-argument",false)]
    [TestCase("base-field-read",false)]
    [TestCase("callback-before-base",false)]
    [TestCase("callback-after-base",false)]
    [TestCase("reordered-fields",false)]
    [TestCase("missing-field",false)]
    [TestCase("ambiguous",false)]
    public void CompleteBaseAndFieldMapsPreserveAllocationOwnerAndEffects(string shape,bool expected)
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var parent=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Proof","Parent",t.SystemObjectType,TypeAttributes.Public);
        var child=new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly,"Proof","Child",parent,TypeAttributes.Public);
        var baseCtor=parent.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,t.SystemStringType,t.SystemInt32Type);
        var ctor=child.InjectMethodContext(".ctor",t.SystemVoidType,MethodAttributes.Public,
            t.SystemStringType,t.SystemInt32Type,t.SystemStringType,t.SystemInt32Type,t.SystemInt32Type);
        var path=child.InjectFieldContext("path",t.SystemStringType,FieldAttributes.Public);path.Offset=24;
        var line=child.InjectFieldContext("line",t.SystemInt32Type,FieldAttributes.Public);line.Offset=32;
        var pos=child.InjectFieldContext("position",t.SystemInt32Type,FieldAttributes.Public);pos.Offset=36;
        var self=Local("this",child);self.IsThis=true;
        var args=ctor.Parameters.Select((p,n)=>Local("p"+n,p.ParameterType)).ToArray();
        ctor.ParameterLocals=[self,..args];
        IOperand firstBase=shape is "shared-base-field-argument" or "shared-base-field-conflict"?args[2]:args[0];
        IOperand secondBase=shape is "base-constant" or "wrong-base-constant"?new Immediate(7):args[1];
        // A constant base argument must not leave a fabricated unused child input.
        if(shape is "base-constant" or "wrong-base-constant")firstBase=args[0];
        var nativeCtor=new List<Instruction>{new(0,OpCode.CallVoid,baseCtor,self,firstBase,secondBase),
            new(1,OpCode.Move,new FieldReference(path,self,path.Offset),args[2]),
            new(2,OpCode.Move,new FieldReference(line,self,line.Offset),args[3]),
            new(3,OpCode.Move,new FieldReference(pos,self,pos.Offset),args[4]),new(4,OpCode.Return)};
        // Keep every input proven: the intentionally shared/constant arguments also
        // populate exact extra fields. No guessed value fills an unused parameter.
        if(shape is "shared-base-field-argument" or "shared-base-field-conflict" or "base-constant" or "wrong-base-constant")
        {
            var retained=child.InjectFieldContext("retained",shape is "base-constant" or "wrong-base-constant"?t.SystemInt32Type:t.SystemStringType,FieldAttributes.Public);
            retained.Offset=40;nativeCtor.Insert(nativeCtor.Count-1,new(5,OpCode.Move,
                new FieldReference(retained,self,40),shape is "base-constant" or "wrong-base-constant"?args[1]:args[0]));
        }
        ctor.ControlFlowGraph=new(nativeCtor);
        var template=InlinedConstructorRecovery.Extract(ctor);
        Assert.That(template,Is.Not.Null);
        Assert.That(template!.BaseArguments,Has.Count.EqualTo(2));
        Assert.That(template.BaseArguments![0].Parameter,Is.EqualTo(firstBase==args[2]?2:0));
        var caller=child.InjectMethodContext("Caller",child,MethodAttributes.Public|MethodAttributes.Static);
        var obj=Local("allocated",child);var allocation=new Instruction(10,OpCode.Newobj,obj,child);
        IOperand baseValue=new StringLiteral(shape is "shared-base-field-argument"?"path":"message");
        if(shape=="late-base-argument")baseValue=Local("late",t.SystemStringType);
        if(shape=="base-field-read")baseValue=new FieldReference(path,Local("elsewhere",child),24);
        var call=new Instruction(11,OpCode.CallVoid,baseCtor,obj,baseValue,new Immediate(7));
        var stores=template.Assignments.Select((a,n)=>new Instruction(12+n,OpCode.Move,
            shape=="raw-stores"?new MemoryOperand(obj,addend:a.Field.Offset):new FieldReference(a.Field,obj,a.Field.Offset),
            a.Parameter switch{0=>new StringLiteral("message"),1=>new Immediate(7),2=>new StringLiteral("path"),
                3=>new Immediate(11),_=>new Immediate(13)})
            {NativeWriteSize=a.Field.FieldType.FullName=="System.String"?8:4}).ToList();
        if(shape=="wrong-base-constant")call.SetOperand(3,new Immediate(8));
        var body=new List<Instruction>{allocation,call};body.AddRange(stores);body.Add(new(30,OpCode.Return,obj));
        if(shape=="missing-base-argument")call.SetOperands(baseCtor,obj,baseValue);
        if(shape=="extra-base-argument")call.SetOperands(baseCtor,obj,baseValue,new Immediate(7),new Immediate(0));
        if(shape=="wrong-base-owner")call.SetOperand(0,t.SystemObjectType.Methods.First(m=>m.Name==".ctor"&&m.Parameters.Count==0));
        if(shape=="late-base-argument")body.Insert(1,new(40,OpCode.Move,baseValue,new StringLiteral("message")));
        if(shape=="callback-before-base")body.Insert(1,new(40,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="callback-after-base")body.Insert(2,new(40,OpCode.CallVoid,new StringLiteral("callback")));
        if(shape=="reordered-fields"){body.Remove(stores[0]);body.Insert(3,stores[0]);}
        if(shape=="missing-field")body.Remove(stores[^1]);
        caller.ControlFlowGraph=new(body);
        var before=caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()).ToArray();
        Assert.That(InlinedConstructorRecovery.Recover(caller,allocation,shape=="ambiguous"?[template,template]:[template]),Is.EqualTo(expected));
        if(!expected)
        {Assert.That(caller.ControlFlowGraph.Instructions.Select(i=>i.ToString()),Is.EqualTo(before));return;}
        Assert.That(call.Operands[0],Is.SameAs(ctor));
        Assert.That(allocation.Operands[1],Is.SameAs(child));
        Assert.That(stores.All(i=>i.OpCode==OpCode.Nop),Is.True);
        Assert.That(call.Operands.Count,Is.EqualTo(7));
        if(shape is not ("valid" or "raw-stores"))
        {
            Assert.That(((StringLiteral)call.Operands[2]).Value,Is.EqualTo("message"));
            Assert.That(((StringLiteral)call.Operands[4]).Value,Is.EqualTo("path"));
            return;
        }
        // Execute the standard proven body against real fixture constructors;
        // the other positive cases above inspect their distinct parameter maps.
        var dynamic=new DynamicMethod("RecoveredConstructor",typeof(ManagedChild),[]);
        var il=dynamic.GetILGenerator();
        foreach(var operand in call.Operands.Skip(2))
            if(operand is StringLiteral text)il.Emit(OpCodes.Ldstr,text.Value);
            else if(operand is Immediate integer)il.Emit(OpCodes.Ldc_I4,(int)integer.Value);
            else throw new System.Exception("unexpected fixture operand");
        il.Emit(OpCodes.Newobj,typeof(ManagedChild).GetConstructors().Single());il.Emit(OpCodes.Ret);
        ManagedParent.Observed.Clear();var run=(System.Func<ManagedChild>)dynamic.CreateDelegate(typeof(System.Func<ManagedChild>));
        var result=run();Assert.That(result.Path,Is.EqualTo("path"));Assert.That(result.Line,Is.EqualTo(11));Assert.That(result.Position,Is.EqualTo(13));
        Assert.That(ManagedParent.Observed,Is.EqualTo(new[]{"message:7:unset:0"}));
    }

    public class ManagedParent
    {
        public static readonly List<string> Observed=[];
        public ManagedParent(string message,int code)
        {var child=(ManagedChild)this;Observed.Add(message+":"+code+":"+(child.Path??"unset")+":"+child.Line);}
    }
    public class ManagedChild:ManagedParent
    {
        public string? Path;public int Line;public int Position;
        public ManagedChild(string message,int code,string path,int line,int position):base(message,code)
        {Path=path;Line=line;Position=position;}
    }
}
