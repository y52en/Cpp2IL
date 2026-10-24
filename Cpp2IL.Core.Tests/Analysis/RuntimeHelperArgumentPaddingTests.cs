using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RuntimeHelperArgumentPaddingTests
{
    private static IEnumerable<TestCaseData> Cases()
    {
        foreach(var name in new[]{"isinst","vm-box","box","checked-unbox"})
        foreach(var shape in new[]{"valid","minimal","wrong-profile","callvoid","virtual","unknown",
            "wrong-address","short","bad-result","memory-padding","address-padding"})
            yield return new TestCaseData(name,shape);
    }

    [TestCaseSource(nameof(Cases))]
    public void OnlyActualKnownAbiPaddingIsRemovedWithoutResolvingTypes(string name,string shape)
    {
        LocalVariable Local(string n)=>new(n,new Register(null,n));
        IOperand target=name switch {
            "isinst"=>new StringLiteral("il2cpp_vm_object_is_inst"),
            "vm-box"=>new StringLiteral("il2cpp_vm_object_box"),
            "box"=>new StringLiteral("il2cpp_value_box"),_=>new Immediate(0xA61E70)
        };
        var value=Local("value");var klass=Local("still_dynamic_class");var result=Local("result");var junk=Local("unused_x2");
        List<IOperand> operands=[target,result,value,klass,junk];
        if(shape=="minimal")operands=operands.Take(4).ToList();
        if(shape=="short")operands=operands.Take(3).ToList();
        if(shape=="unknown")operands[0]=new StringLiteral("unknown_function");
        if(shape=="wrong-address")operands[0]=new Immediate(0xA61E60);
        if(shape=="bad-result")operands[1]=new Immediate(0);
        if(shape=="memory-padding")operands[4]=new MemoryOperand(value);
        if(shape=="address-padding")operands[4]=new AddressOf(value);
        var call=new Instruction(7,shape=="callvoid"?OpCode.CallVoid:OpCode.Call,operands){NativeVirtualDispatch=shape=="virtual"};
        var before=call.Operands.ToArray();var opcode=call.OpCode;
        var changed=RuntimeHelperArgumentPaddingRecovery.TryTrim(call,shape!="wrong-profile");
        Assert.That(changed,Is.EqualTo(shape=="valid"));
        Assert.That(call.Operands,Is.EqualTo(changed?before[..4]:before));
        Assert.That(call.OpCode,Is.EqualTo(opcode));
        Assert.That(klass.Type,Is.Null,"dynamic metadata must not become a guessed static CIL token");
    }

    [Test]
    public void ProductionRejectsADifferentActualGameImage()
    {
        var app=TestGameLoader.LoadSimple2019Game();var t=app.SystemTypes;
        var method=new InjectedMethodAnalysisContext(t.SystemObjectType,"ForeignImage",t.SystemVoidType,
            MethodAttributes.Public|MethodAttributes.Static,[]);
        var call=new Instruction(0,OpCode.Call,new StringLiteral("il2cpp_vm_object_is_inst"),
            new LocalVariable("result",new Register(null,"result")),new Immediate(0),new Immediate(0),new Immediate(0));
        method.ControlFlowGraph=new([call,new(1,OpCode.Return)]);
        Assert.That(RuntimeHelperArgumentPaddingRecovery.Run(method),Is.Zero);
        Assert.That(call.Operands.Count,Is.EqualTo(5));
    }
}
