using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Native bodies, not the existence of a parameterless metadata signature,
// prove that an Object-base constructor can stand in for this allocated type.
public static class TrivialConstructorRecovery
{
    public const string CacheKey = "NativeTrivialConstructorTemplates";
    public const string ObjectProofKey = "NativeObjectConstructorIsNoOp";
    public sealed record Template(MethodAnalysisContext Constructor, MethodAnalysisContext? ForwardedBase = null);
    public sealed record ObjectProof(bool IsNoOp);

    // Resolve the allocation's own metadata operand, never infer the allocation
    // from a result local that later propagation can widen to a base class.
    public static TypeAnalysisContext? AllocationType(IOperand operand) => operand switch
    {
        LocalVariable { Type: RuntimeClassTypeAnalysisContext runtime } => runtime.RepresentedType,
        RuntimeClassTypeAnalysisContext runtime => runtime.RepresentedType,
        TypeAnalysisContext type => type,
        _ => null,
    };

    public static bool SameType(TypeAnalysisContext? left, TypeAnalysisContext? right)
    {
        if (left == null || right == null) return false;
        if (ReferenceEquals(left, right)) return true;
        // Resolving a generic argument can create a fresh SZARRAY wrapper.
        // Compare its exact element metadata identity, never its display name.
        // Do not conflate SZARRAY with rank-one multidimensional ARRAY.
        if (left is SzArrayTypeAnalysisContext la && right is SzArrayTypeAnalysisContext ra)
            return SameType(la.ElementType, ra.ElementType);
        return left is GenericInstanceTypeAnalysisContext a && right is GenericInstanceTypeAnalysisContext b
            && ReferenceEquals(a.GenericType, b.GenericType) && a.GenericArguments.Count == b.GenericArguments.Count
            && a.GenericArguments.Zip(b.GenericArguments, SameType).All(equal => equal);
    }

    public static MethodAnalysisContext? BindConstructorOwner(MethodAnalysisContext constructor, TypeAnalysisContext allocation)
    {
        if (constructor.Name != ".ctor" || constructor.IsStatic) return null;
        if (SameType(constructor.DeclaringType, allocation)) return constructor;
        // A known constructor on the exact generic definition needs the already
        // known allocation arguments, not a guessed owner or a different body.
        if (allocation is GenericInstanceTypeAnalysisContext generic
            && ReferenceEquals(constructor.DeclaringType, generic.GenericType) && constructor.GenericParameters.Count == 0)
            return new ConcreteGenericMethodAnalysisContext(constructor, generic.GenericArguments, []);
        return null;
    }

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if (constructor.IsStatic || constructor.Name != ".ctor" || !constructor.IsVoid
            || constructor.Parameters.Count != 0 || constructor.DeclaringType?.IsValueType != false
            || constructor.ControlFlowGraph == null) return null;
        var cfg = constructor.ControlFlowGraph;
        var visited = new HashSet<Block>();
        var current = cfg.EntryBlock;
        while (visited.Add(current) && !ReferenceEquals(current, cfg.ExitBlock))
        {
            if (current.Successors.Count != 1) return null;
            current = current.Successors[0];
        }
        if (!ReferenceEquals(current, cfg.ExitBlock)) return null;
        visited.Add(cfg.ExitBlock);
        if (cfg.Blocks.Any(b => !visited.Contains(b))) return null;
        var objectConstructor = constructor.DeclaringType.FullName == "System.Object";
        var returned = false;
        var baseCalls = 0;
        MethodAnalysisContext? forwardedBase = null;
        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
            if (instruction is { OpCode: OpCode.Return, Operands.Count: 0 })
            { if (returned) return null; returned = true; continue; }
            if (returned || objectConstructor) return null;
            // A complete native constructor can forward to its direct base,
            // even when that base has observable work. Preserve the exact call;
            // do not treat the base as empty or substitute an arbitrary ancestor.
            // Open generic base contexts need separate instantiation evidence.
            if (instruction is { OpCode: OpCode.CallVoid, NativeVirtualDispatch: false,
                    Operands: [MethodAnalysisContext directBase, LocalVariable { IsThis: true }] }
                && directBase.Name == ".ctor" && !directBase.IsStatic && !directBase.IsVirtual && directBase.IsVoid
                && directBase.Parameters.Count == 0 && directBase.DeclaringType?.FullName != "System.Object"
                && constructor.DeclaringType.GenericParameters.Count == 0
                && directBase.DeclaringType is { GenericParameters.Count: 0, IsGenericInstance: false }
                && SameType(constructor.DeclaringType.BaseType, directBase.DeclaringType) && ++baseCalls == 1)
            { forwardedBase = directBase; continue; }
            if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext baseConstructor, LocalVariable { IsThis: true }] }
                && baseConstructor.Name == ".ctor" && baseConstructor.Parameters.Count == 0
                && baseConstructor.DeclaringType?.FullName == "System.Object"
                && baseConstructor.GetExtraData<ObjectProof>(ObjectProofKey) is { IsNoOp: true } && ++baseCalls == 1) continue;
            // Includes stores, callback calls, reads, custom exceptions and conditional construction.
            return null;
        }
        return returned ? new(constructor, forwardedBase) : null;
    }

    public static int Prepare(ApplicationAnalysisContext app, Func<MethodAnalysisContext, bool> skip)
    {
        // Called once before parallel IL emission. Never analyze from a caller's worker.
        var objectConstructors = app.SystemTypes.SystemObjectType.Methods
            .Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 0 && m.UnderlyingPointer != 0).ToArray();
        foreach (var constructor in objectConstructors)
        {
            constructor.PutExtraData(ObjectProofKey, new ObjectProof(false));
            try
            {
                constructor.EnsureRawBytes();
                if (constructor.RawBytes.Length == 0 || constructor.RawBytes.Length > 512) continue;
                constructor.Analyze();
                constructor.PutExtraData(ObjectProofKey, new ObjectProof(Extract(constructor) != null));
            }
            catch { /* Missing/incomplete native proof never authorizes rewriting. */ }
            finally { constructor.ReleaseAnalysisData(); }
        }
        var count = 0;
        foreach (var type in app.Assemblies.SelectMany(a => a.Types))
        {
            if (type.IsValueType || type.FullName == "System.Object") continue;
            var templates = new List<Template>();
            var constantTemplates = new List<ConstantFieldConstructorRecovery.Template>();
            var forwardingTemplates = new List<ForwardedConstructorRecovery.Template>();
            var argumentTemplates = new List<ArgumentForwardingConstructorRecovery.Template>();
            foreach (var constructor in type.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic
                && m.Parameters.Count <= 8 && m.UnderlyingPointer != 0))
            {
                if (skip(constructor)) continue;
                try
                {
                    constructor.EnsureRawBytes();
                    if (constructor.RawBytes.Length == 0 || constructor.RawBytes.Length > 512) continue;
                    constructor.Analyze();
                    if (Extract(constructor) is { } template) templates.Add(template);
                    if (ConstantFieldConstructorRecovery.Extract(constructor) is { } constant) constantTemplates.Add(constant);
                    if (ForwardedConstructorRecovery.Extract(constructor) is { } forwarding) forwardingTemplates.Add(forwarding);
                    if (ArgumentForwardingConstructorRecovery.Extract(constructor) is { } arguments) argumentTemplates.Add(arguments);
                }
                catch { /* Keep unsupported constructors diagnostic, including generic contexts. */ }
                finally { constructor.ReleaseAnalysisData(); }
            }
            type.PutExtraData(CacheKey, templates.ToArray());
            type.PutExtraData(ConstantFieldConstructorRecovery.CacheKey, constantTemplates.ToArray());
            type.PutExtraData(ForwardedConstructorRecovery.CacheKey, forwardingTemplates.ToArray());
            type.PutExtraData(ArgumentForwardingConstructorRecovery.CacheKey, argumentTemplates.ToArray());
            count += templates.Count;
        }
        return count;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph == null) return 0;
        var count = 0;
        foreach (var allocation in method.ControlFlowGraph.Instructions.ToArray())
        {
            if (allocation is not { OpCode: OpCode.Newobj, Operands: [LocalVariable obj, TypeAnalysisContext allocated] }) continue;
            var definition = allocated is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : allocated;
            var templates = definition.GetExtraData<Template[]>(CacheKey);
            if (templates is not { Length: 1 }) continue;
            var target = templates[0].Constructor;
            if (allocated is GenericInstanceTypeAnalysisContext generic)
                target = new ConcreteGenericMethodAnalysisContext(target, generic.GenericArguments, []);
            if (!SameType(target.DeclaringType, allocated)) continue;
            if (Recover(method, allocation, obj, target, templates[0].ForwardedBase)) count++;
        }
        return count;
    }

    public static bool Recover(MethodAnalysisContext method, Instruction allocation, LocalVariable obj, MethodAnalysisContext target,
        MethodAnalysisContext? forwardedBase = null)
    {
        if (method.ControlFlowGraph == null || target.Parameters.Count != 0
            || allocation.Operands is not [_, TypeAnalysisContext allocated] || !SameType(target.DeclaringType, allocated)) return false;
        var block = method.ControlFlowGraph.Blocks.SingleOrDefault(b => b.Instructions.Contains(allocation));
        if (block == null) return false;
        var position = block.Instructions.IndexOf(allocation) + 1;
        var visited = new HashSet<Block>();
        var aliases = new HashSet<LocalVariable> { obj };
        while (visited.Add(block))
        {
            foreach (var instruction in block.Instructions.Skip(position))
            {
                if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable alias, LocalVariable source] }
                    && aliases.Contains(source)) { aliases.Add(alias); continue; }
                if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext baseConstructor, LocalVariable receiver] }
                    && aliases.Contains(receiver) && baseConstructor.Name == ".ctor"
                    && !instruction.NativeVirtualDispatch
                    && (forwardedBase != null ? ReferenceEquals(baseConstructor, forwardedBase)
                        : baseConstructor.DeclaringType?.FullName == "System.Object"
                            && baseConstructor.GetExtraData<ObjectProof>(ObjectProofKey) is { IsNoOp: true }))
                { instruction.SetOperands(target, receiver); return true; }
                return false; // Do not reorder construction over any observable work.
            }
            if (block.Successors.Count != 1 || block.Successors[0].Predecessors.Count != 1) return false;
            block = block.Successors[0]; position = 0;
        }
        return false;
    }
}
