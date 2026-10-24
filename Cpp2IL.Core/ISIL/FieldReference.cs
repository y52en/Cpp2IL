using System.Collections.Generic;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;
    public FieldReference? Parent;

    // Parent links describe the same object's nested storage. Copy/SSA folds
    // must update matching receiver identities throughout the path, not leave
    // a stale parent which the IL emitter later reads instead of the leaf.
    public void ReplaceLocal(LocalVariable previous, LocalVariable replacement)
    {
        var seen = new HashSet<FieldReference>();
        for (var current = this; current != null && seen.Add(current); current = current.Parent)
            if (ReferenceEquals(current.Local, previous))
                current.Local = replacement;
    }

    public override string ToString() => Parent==null ? $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})" : $"{Parent}.{Field.Name} ({Field.FieldType.FullName})";
}
