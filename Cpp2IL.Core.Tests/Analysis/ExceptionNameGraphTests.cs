using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class ExceptionNameGraphTests
{
    [Test]
    public void DepthLimitedSubqueryDoesNotPoisonAShallowerPath()
    {
        var graph = new Dictionary<ulong, ThrowHelperRecovery.ExceptionHelperNode>
        {
            [1] = new(null, [2, 5]), [2] = new(null, [3]), [3] = new(null, [4]),
            [4] = new(null, [5]), [5] = new(null, [6]), [6] = new("NotSupportedException", [])
        };
        Assert.That(ThrowHelperRecovery.ResolveNameGraph(1, a => graph.GetValueOrDefault(a)), Is.EqualTo("NotSupportedException"));
    }

    [Test]
    public void CycleGuardIsLocalToTheActivePath()
    {
        var graph = new Dictionary<ulong, ThrowHelperRecovery.ExceptionHelperNode>
        { [1] = new(null, [2, 3]), [2] = new(null, [1]), [3] = new("NullReferenceException", []) };
        Assert.That(ThrowHelperRecovery.ResolveNameGraph(1, a => graph.GetValueOrDefault(a)), Is.EqualTo("NullReferenceException"));
    }

    [Test]
    public void UnknownNodeAndOverDepthRemainUnresolved()
    {
        ThrowHelperRecovery.ExceptionHelperNode? Inspect(ulong address) => address < 6
            ? new(null, [address + 1]) : new("Exception", []);
        Assert.That(ThrowHelperRecovery.ResolveNameGraph(1, Inspect), Is.Null);
        Assert.That(ThrowHelperRecovery.ResolveNameGraph(1, _ => null), Is.Null);
    }

    [Test]
    public void ConcurrentRootsDoNotShareProvisionalOrDepthDependentAnswers()
    {
        var answers = new string?[128];
        Parallel.For(0, answers.Length, i => answers[i] = ThrowHelperRecovery.ResolveNameGraph(1,
            a => a == 1 ? new(null, [2]) : new("NullReferenceException", [])));
        Assert.That(answers.All(name => name == "NullReferenceException"), Is.True);
    }
}
