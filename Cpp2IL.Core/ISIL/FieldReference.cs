using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;
    public FieldReference? Parent;

    public override string ToString() => Parent==null ? $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})" : $"{Parent}.{Field.Name} ({Field.FieldType.FullName})";
}
