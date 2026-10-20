using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Finds exception throw helper functions. These eventually look up the type they throw by name
/// (via <c>Class::FromName(corlib, "System", "NullReferenceException")</c>), so the type name appears
/// as a plain C string in the helper's body.
/// </summary>
public static class ThrowHelperRecovery
{
    private const int MaxDepth = 5;
    private const int MaxRaiserDepth = 3;
    private const int MaxStringLength = 64;

    public static TypeAnalysisContext? GetThrownException(ApplicationAnalysisContext appContext, ulong address)
    {
        // Publish only a completed ROOT query. Provisional nulls, cycle guards
        // and depth-limited subqueries must never become other workers' answers.
        var name = appContext.ThrowHelperNamesByAddress.GetOrAdd(address, root => ResolveNameGraph(root, candidate =>
        {
            if (!appContext.InstructionSet.HasExceptionWrapperShape(appContext, candidate)) return null;
            var (references, calls) = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, candidate);
            if (calls.Any(target => appContext.MethodsByAddress.ContainsKey(target))) return null;
            var targets = calls.ToList();
            var thunk = appContext.InstructionSet.GetThunkTarget(appContext, candidate);
            if (thunk != 0 && !targets.Contains(thunk)) targets.Add(thunk);
            return new ExceptionHelperNode(FindExceptionName(appContext, references), targets);
        }));

        if (name == null)
            return null;

        var type = appContext.LibCpp2IlContext.ReflectionCache.GetType(name);

        return type == null ? null : appContext.ResolveContextForType(type);
    }

    // Whether the provided method raises whatever exception it is handed
    // e.g. il2cpp_codegen_raise_exception, il2cpp_codegen_rethrow_exception, vm::Exception::Raise
    public static bool IsExceptionRaiser(ApplicationAnalysisContext appContext, ulong address)
    {
        if (address == 0)
            return false;

        if (appContext.ExceptionRaisersByAddress.TryGetValue(address, out var cached))
            return cached;

        var keys = appContext.GetOrCreateKeyFunctionAddresses();
        var raises = new HashSet<ulong> { keys.il2cpp_raise_exception,
            keys.il2cpp_vm_exception_raise, keys.il2cpp_codegen_raise_exception };
        raises.Remove(0);
        if (raises.Count == 0)
            return false;
        // A bounded scan past a noreturn call can encounter the next function's
        // ordinary corlib lookup. That last call is NOT evidence of throwing.
        // Reach the positively identified raiser itself, never an inferred
        // final callee of its surrounding byte window.
        var result = ReachesCall(appContext, address, raises, 0, []);

        appContext.ExceptionRaisersByAddress[address] = result;
        return result;
    }

    private static bool ReachesCall(ApplicationAnalysisContext appContext, ulong address, ISet<ulong> raises, int depth, HashSet<ulong> visited)
    {
        if (raises.Contains(address))
            return true;

        if (depth >= MaxRaiserDepth || !visited.Add(address)
            || !appContext.InstructionSet.HasExceptionWrapperShape(appContext, address))
            return false;

        var (_, callTargets) = appContext.InstructionSet.InspectPotentialThrowHelper(appContext, address);

        // Only the last transport call can establish an unconditional raise.
        // A function which merely calls a throwing routine along some path is not a raiser.
        var last = callTargets.LastOrDefault();
        var thunk = appContext.InstructionSet.GetThunkTarget(appContext, address);
        return (thunk != 0 && ReachesCall(appContext, thunk, raises, depth + 1, visited))
            || (last != 0 && ReachesCall(appContext, last, raises, depth + 1, visited));
    }

    internal readonly record struct ExceptionHelperNode(string? Name, IReadOnlyList<ulong> Targets);

    internal static string? ResolveNameGraph(ulong root, Func<ulong, ExceptionHelperNode?> inspect)
    {
        var path = new HashSet<ulong>();
        return Walk(root, 0);
        string? Walk(ulong address, int depth)
        {
            if (address == 0 || depth >= MaxDepth || !path.Add(address)) return null;
            try
            {
                if (inspect(address) is not { } node) return null;
                if (node.Name != null) return node.Name;
                foreach (var target in node.Targets)
                    if (Walk(target, depth + 1) is { } name) return name;
                return null;
            }
            finally { path.Remove(address); }
        }
    }

    private static string? FindExceptionName(ApplicationAnalysisContext appContext, IReadOnlyList<ulong> dataReferences)
    {
        foreach (var address in dataReferences)
            if (ReadCStringAtVirtualAddress(appContext, address) is { } text && text.EndsWith("Exception", StringComparison.Ordinal))
                return text;

        return null;
    }

    //TODO didn't we have a helper for this somewhere? Can't find it. Maybe got deleted. Maybe it's just too late
    internal static string? ReadCStringAtVirtualAddress(ApplicationAnalysisContext appContext, ulong address, int maxLength = MaxStringLength)
    {
        long offset;

        try
        {
            offset = appContext.Binary.MapVirtualAddressToRaw(address, false);
        }
        catch
        {
            return null;
        }

        if (offset <= 0)
            return null;

        var content = appContext.Binary.GetRawBinaryContent();
        var end = offset;

        while (end < content.Length && end - offset < maxLength && content[(int)end] != 0)
        {
            var c = content[(int)end];

            if (c < 32 || c >= 127)
                return null;

            end++;
        }

        if (end == offset || end >= content.Length || content[(int)end] != 0)
            return null;

        var characters = new char[end - offset];

        for (var i = 0; i < characters.Length; i++)
            characters[i] = (char)content[(int)offset + i];

        return new string(characters);
    }
}
