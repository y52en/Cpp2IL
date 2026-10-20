using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RuntimeHandlePhiTests
{
    [TestCase("static", "unknown", false)]
    [TestCase("static", "same", true)]
    [TestCase("static", "different", false)]
    [TestCase("static", "managed", false)]
    [TestCase("static", "constant", false)]
    [TestCase("class", "unknown", false)]
    [TestCase("class", "same", true)]
    [TestCase("class", "different", false)]
    [TestCase("class", "managed", false)]
    [TestCase("static", "backward", false)]
    [TestCase("method", "unknown", false)]
    [TestCase("method", "same", true)]
    [TestCase("method", "different", false)]
    [TestCase("method", "backward", false)]
    [TestCase("field", "unknown", false)]
    [TestCase("field", "same", true)]
    [TestCase("field", "different", false)]
    [TestCase("field", "backward", false)]
    [TestCase("managed", "unknown", true)]
    public void MetadataPointerProvenanceRequiresEveryIncomingEdge(string kind, string shape, bool expected)
    {
        var t = TestGameLoader.LoadSimple2019Game().SystemTypes;
        var firstMethod = new InjectedMethodAnalysisContext(t.SystemObjectType, "First", t.SystemVoidType, System.Reflection.MethodAttributes.Public, []);
        var secondMethod = new InjectedMethodAnalysisContext(t.SystemObjectType, "Second", t.SystemVoidType, System.Reflection.MethodAttributes.Public, []);
        var holder = new InjectedTypeAnalysisContext(t.SystemObjectType.DeclaringAssembly, "Test", "Holder", t.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var firstField = holder.InjectFieldContext("First", t.SystemInt32Type, System.Reflection.FieldAttributes.Public);
        var secondField = holder.InjectFieldContext("Second", t.SystemInt32Type, System.Reflection.FieldAttributes.Public);
        TypeAnalysisContext Make(TypeAnalysisContext owner) => kind switch
        {
            "static" => new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly),
            "class" => new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly),
            "method" => new RuntimeMethodInfoAnalysisContext(ReferenceEquals(owner, t.SystemStringType) ? firstMethod : secondMethod, owner.DeclaringAssembly),
            "field" => new RuntimeFieldInfoAnalysisContext(ReferenceEquals(owner, t.SystemStringType) ? firstField : secondField, owner.DeclaringAssembly),
            _ => owner
        };
        var first = new LocalVariable("first", new(null, "first"), Make(t.SystemStringType));
        var second = new LocalVariable("second", new(null, "second"), shape switch
        {
            "same" => Make(t.SystemStringType), "different" => Make(t.SystemObjectType),
            "managed" => t.SystemStringType, _ => null
        });
        var result = new LocalVariable("result", new(null, "result"), shape == "backward" ? Make(t.SystemStringType) : null);
        IOperand input = shape == "constant" ? new Immediate(0) : second;
        var phi = new Instruction(-1, OpCode.Phi, result, first, input);
        Assert.That(LocalVariables.PropagatePhi(phi), Is.EqualTo(expected));
        Assert.That(result.Type != null, Is.EqualTo(expected || shape == "backward"));
        if (kind != "managed" && shape is "unknown" or "backward") Assert.That(second.Type, Is.Null);
        if (expected) Assert.That(result.Type?.FullName, Is.EqualTo(first.Type!.FullName));
    }
}
