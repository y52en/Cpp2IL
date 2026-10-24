using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class ExplicitSequentialValueSizeTests
{
    [TestCase(8,8,8,true)]
    [TestCase(12,12,12,true)]
    [TestCase(16,16,16,true)]
    [TestCase(0,8,8,true)]
    [TestCase(-1,8,8,true)]
    [TestCase(16,8,16,false)]
    [TestCase(16,8,8,false)]
    [TestCase(8,8,16,false)]
    [TestCase(8,12,12,false)]
    [TestCase(-2,8,8,false)]
    [TestCase(0,0,0,false)]
    public void DeclaredComputedAndNativeFootprintsMustAgree(int declared,int computed,int native,bool expected)
        => Assert.That(GenericInstanceFieldLayout.CompleteValueSizeAgrees(declared,computed,native),Is.EqualTo(expected));
}
