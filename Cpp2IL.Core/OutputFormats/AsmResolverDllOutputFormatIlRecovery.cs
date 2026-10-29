using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AssetRipper.CIL;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.OutputFormats;

public class AsmResolverDllOutputFormatIlRecovery : AsmResolverDllOutputFormat
{
    public override string OutputFormatId => "dll_il_recovery";

    public override string OutputFormatName => "DLL files with IL Recovery";

    public override List<AssemblyDefinition> BuildAssemblies(ApplicationAnalysisContext context)
    {
        //We're going to need key function addresses, so grab them. This way the logging is more consistent
        Logger.InfoNewline("Finding key function addresses...");
        var start = DateTime.Now;
        _ = context.GetOrCreateKeyFunctionAddresses();
        Logger.InfoNewline($"Key function addresses found in {DateTime.Now.Subtract(start).TotalMilliseconds}ms");

        IlGenerator.InjectHelpersType(context);

        return base.BuildAssemblies(context);
    }

    protected override void PrepareMethodBodies(ApplicationAnalysisContext context)
    {
        var fieldMethodCount = InlinedFieldMethodRecovery.Prepare(context, method =>
            SkipAssemblyRecovery(method.DeclaringType!.DeclaringAssembly.Name + ".dll", method.UnderlyingPointer,
                Environment.GetEnvironmentVariable("CPP2IL_RECOVERY_INCLUDE_FRAMEWORKS") == "1"));
        Logger.InfoNewline($"Prepared {fieldMethodCount} native-derived inline field method templates.");
        var trivialCount = TrivialConstructorRecovery.Prepare(context, ctor =>
            SkipAssemblyRecovery(ctor.DeclaringType!.DeclaringAssembly.Name + ".dll", ctor.UnderlyingPointer,
                Environment.GetEnvironmentVariable("CPP2IL_RECOVERY_INCLUDE_FRAMEWORKS") == "1"));
        Logger.InfoNewline($"Prepared {trivialCount} native-proven trivial constructor templates.");
        // Build immutable templates before parallel emission, which mutates/releases
        // method graphs. Never analyze a constructor concurrently from a caller.
        var count = 0;
        foreach (var type in context.Assemblies.SelectMany(a => a.Types))
        {
            var templates = new List<InlinedConstructorRecovery.Template>();
            var structural = new List<StructuralConstructorRecovery.Template>();
            var baseInitializers = new List<ParameterizedBaseInitializerRecovery.Template>();
            if (type.IsValueType || type.BaseType==null || type.HasAnyGenericParameters()) continue;
            foreach (var ctor in type.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic
                && m.UnderlyingPointer != 0 && m.Parameters.Count <= 8))
            {
                if (SkipAssemblyRecovery(type.DeclaringAssembly.Name + ".dll", ctor.UnderlyingPointer,
                    Environment.GetEnvironmentVariable("CPP2IL_RECOVERY_INCLUDE_FRAMEWORKS") == "1")) continue;
                try
                {
                    ctor.EnsureRawBytes();
                    if (ctor.RawBytes.Length > 512) continue;
                    ctor.Analyze();
                    if (InlinedConstructorRecovery.Extract(ctor) is { } template) templates.Add(template);
                    // Constant-only parameterless templates use the same complete
                    // native base-call/store proof. Other template families keep
                    // their existing nonempty-parameter input contract.
                    if (ctor.Parameters.Count > 0)
                    {
                        if (StructuralConstructorRecovery.Extract(ctor) is { } shape) structural.Add(shape);
                        if (ParameterizedBaseInitializerRecovery.Extract(ctor) is { } initializer) baseInitializers.Add(initializer);
                    }
                }
                catch { /* Unproved constructors remain unmodified and diagnostic. */ }
                finally { ctor.ReleaseAnalysisData(); }
            }
            type.PutExtraData(InlinedConstructorRecovery.CacheKey, templates.ToArray());
            type.PutExtraData(StructuralConstructorRecovery.CacheKey, structural.ToArray());
            type.PutExtraData(ParameterizedBaseInitializerRecovery.CacheKey, baseInitializers.ToArray());
            count += templates.Count;
        }
        Logger.InfoNewline($"Prepared {count} pure field-initialization constructor templates.");
    }

    protected override void FillMethodBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        var module = methodDefinition.DeclaringModule!;
        var moduleName = module.Name!.ToString();
        var shouldSkip = SkipAssemblyRecovery(moduleName, methodContext.UnderlyingPointer,
            Environment.GetEnvironmentVariable("CPP2IL_RECOVERY_INCLUDE_FRAMEWORKS") == "1");

        if (!methodDefinition.IsManagedMethodWithBody())
            return;

        methodDefinition.CilMethodBody = new();
        var instructions = methodDefinition.CilMethodBody.Instructions;

        if (shouldSkip)
        {
            FillMethodBodyWithStub(methodDefinition);
            return;
        }

        try
        {
            Interlocked.Increment(ref TotalMethodCount);

            methodContext.Analyze();
            UnusedInstanceReceiverRecovery.Run(methodContext);

            InlinedConstructorRecovery.Run(methodContext);
            StructuralConstructorRecovery.Run(methodContext);
            TrivialConstructorRecovery.Run(methodContext);
            ForwardedConstructorRecovery.Run(methodContext);
            MergedAllocationRecovery.Run(methodContext);
            ArgumentForwardingConstructorRecovery.Run(methodContext);
            ConstantFieldConstructorRecovery.Run(methodContext);
            ParameterizedBaseInitializerRecovery.Run(methodContext);
            EmptyObjectBaseConstructorRecovery.Run(methodContext);
            ConstructorPrologueRecovery.Run(methodContext);
            ZeroStateConstructorRecovery.Run(methodContext);
            // Constructor reconstruction consumes allocation-adjacent stores;
            // do not hide those stores behind setters before it has run.
            InlinedFieldMethodRecovery.Run(methodContext);

            if (methodContext.ConvertedIsil.Count == 0)
                throw new DecompilerException("No native instructions were recovered.");
            else
                IlGenerator.GenerateIl(methodContext, methodDefinition);

            //WriteControlFlowGraph(methodContext, Path.Combine(Environment.CurrentDirectory, "Cpp2IL", "bin", "Debug", "net9.0", "cpp2il_out", "cfg"));

            Interlocked.Increment(ref SuccessfulMethodCount);
        }
        catch (Exception e)
        {
            // Known analysis limitations (DecompilerException) get a one-line warning; anything
            // else is an unexpected bug and keeps its (collapsed) stack trace.
            var detail = e is DecompilerException ? e.Message : e.ToCollapsedString();

            if (detail.Length > 1000) // unbounded ldstrs can overflow the 24 bit #US heap offset space
                detail = detail[..1000] + "…";

            if (e is DecompilerException)
                Logger.WarnNewline($"Skipping {methodContext.FullName}: {e.Message}");
            else
                Logger.ErrorNewline($"Decompiling {methodContext.FullName} failed: {detail}");
            
            methodDefinition.CilMethodBody = new();
            instructions = methodDefinition.CilMethodBody.Instructions;

            var factory = module.CorLibTypeFactory;
            var exceptionCtor = factory.CorLibScope
                .CreateTypeReference("System", "Exception")
                .CreateMemberReference(".ctor", MethodSignature.CreateInstance(factory.Void, [factory.String]));

            instructions.Add(CilOpCodes.Ldstr, "Cpp2IL recovery failure: " + detail);
            instructions.Add(CilOpCodes.Newobj, exceptionCtor);
            instructions.Add(CilOpCodes.Throw);
        }

        methodContext.ReleaseAnalysisData();
    }

    // Explicit opt-in for native-backed framework methods only. A method
    // without an original entry must remain a stub rather than fabricate IL.
    internal static bool SkipAssemblyRecovery(string moduleName, ulong originalPointer, bool includeFrameworks)
    {
        var framework = moduleName.StartsWith("UnityEngine.") || moduleName.StartsWith("Unity.")
            || moduleName.StartsWith("System.") || moduleName == "System" || moduleName.StartsWith("mscorlib");
        return framework && !(includeFrameworks && originalPointer != 0);
    }

    public static void WriteControlFlowGraph(MethodAnalysisContext method, string outputPath)
    {
        var graph = method.ControlFlowGraph;

        var sb = new StringBuilder();
        var edges = new List<(int, int)>();

        sb.AppendLine("digraph ControlFlowGraph {");
        sb.AppendLine("    \"label\"=\"Control flow graph\"");

        // no instructions
        graph ??= new ISILControlFlowGraph([]);

        var methodText = $@"{CsFileUtils.GetKeyWordsForMethod(method)} {method.FullNameWithSignature}
parameter locals: {string.Join(", ", method.ParameterLocals)}
parameter operands: {string.Join(", ", method.ParameterOperands)}";

        foreach (var block in graph.Blocks)
        {
            if (block == graph.EntryBlock || block == graph.ExitBlock)
            {
                var isEntry = block == graph.EntryBlock;
                sb.AppendLine($"""
                               	{block.ID} [
                               		"color"="{(isEntry ? "green" : "red")}"
                               		"label"="{(isEntry ? $"Entry ({block.ID})\n{methodText}" : $"Exit ({block.ID})")}"
                               	]
                               """);
            }
            else
            {
                sb.AppendLine($"""
                               	{block.ID} [
                               		"shape"="box"
                               		"label"="{block.ToString().EscapeString().Replace("\\r", "")}"
                               	]
                               """);
            }

            edges.AddRange(block.Successors.Select(b => (block.ID, b.ID)));
        }

        foreach (var edge in edges)
            sb.AppendLine($"    {edge.Item1} -> {edge.Item2}");

        sb.AppendLine("}");

        var type = method.DeclaringType!;
        var assemblyName = MiscUtils.CleanPathElement(type.DeclaringAssembly.CleanAssemblyName);
        var typePath = Path.Combine(type.FullName.Split('.').Select(MiscUtils.CleanPathElement).ToArray());
        var directoryPath = Path.Combine(outputPath, assemblyName, typePath);

        var methodName = MiscUtils.CleanPathElement(method.Name + "_" + string.Join("_",
            method.Parameters.Select(p => MiscUtils.CleanPathElement(p.ParameterType.Name))));
        var path = Path.Combine(directoryPath, methodName) + ".dot";

        if (path.Length > 260)
        {
            path = path[..250];
            path += ".dot";
        }

        var directory = Path.GetDirectoryName(path)!;
        if (!Directory.Exists(directory))
            Directory.CreateDirectory(directory);

        File.WriteAllText(path, sb.ToString());
    }
}
