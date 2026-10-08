using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public sealed record DefaultStructValue(TypeAnalysisContext Type) : IOperand
{
    public override string ToString()=>"default("+Type.FullName+")";
}
