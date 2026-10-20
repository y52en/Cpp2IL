using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class OpenTypeRgctxTests
{
    [Test]
    public void OpenOwnerKeepsItsOwnGenericParameters()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "Owner", app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, owner);
        owner.GenericParameters.Add(parameter);
        var arguments = RgctxResolver.TypeArgumentsForOwner(owner);
        Assert.That(arguments.Count, Is.EqualTo(1));
        Assert.That(arguments[0], Is.SameAs(parameter));
        Assert.That(GenericInstantiation.Instantiate(parameter, arguments, []), Is.SameAs(parameter));
        Assert.That(((SzArrayTypeAnalysisContext)GenericInstantiation.Instantiate(new SzArrayTypeAnalysisContext(parameter), arguments, [])).ElementType,
            Is.SameAs(parameter));
    }

    [Test]
    public void ConcreteAndNonGenericOwnersDoNotAcquireGuessedArguments()
    {
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Test", "Owner", app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, owner);
        owner.GenericParameters.Add(parameter);
        var concrete = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemStringType]);
        Assert.That(RgctxResolver.TypeArgumentsForOwner(concrete)[0], Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(GenericInstantiation.Instantiate(parameter, RgctxResolver.TypeArgumentsForOwner(concrete), []),
            Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(RgctxResolver.TypeArgumentsForOwner(app.SystemTypes.SystemObjectType), Is.Empty);
        Assert.That(owner.GenericParameters[0], Is.SameAs(parameter));
    }
}
