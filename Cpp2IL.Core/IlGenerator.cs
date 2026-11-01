using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using ElementType = AsmResolver.PE.DotNet.Metadata.Tables.ElementType;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core;

public static class IlGenerator
{
    private const string HelpersNamespace = "Cpp2ILInjected";
    private const string HelpersTypeName = "Cpp2ILHelpers";
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    // Primitive array opcodes give the evaluation stack its CLI normalized
    // type (for example Char/UInt16 -> int32), with the declared load/store
    // width and signedness. Do not substitute enum/struct/generic/reference
    // element tokens: their exact type contract must stay explicit.
    internal static void EmitArrayElement(CilInstructionCollection instructions, TypeSignature type, bool store)
    {
        CilOpCode? primitive = type is CorLibTypeSignature core ? (store ? core.ElementType switch
        {
            ElementType.Boolean or ElementType.I1 or ElementType.U1 => CilOpCodes.Stelem_I1,
            ElementType.Char or ElementType.I2 or ElementType.U2 => CilOpCodes.Stelem_I2,
            ElementType.I4 or ElementType.U4 => CilOpCodes.Stelem_I4,
            ElementType.I8 or ElementType.U8 => CilOpCodes.Stelem_I8,
            ElementType.I or ElementType.U => CilOpCodes.Stelem_I,
            ElementType.R4 => CilOpCodes.Stelem_R4,
            ElementType.R8 => CilOpCodes.Stelem_R8,
            _ => (CilOpCode?)null
        } : core.ElementType switch
        {
            ElementType.I1 => CilOpCodes.Ldelem_I1,
            ElementType.Boolean or ElementType.U1 => CilOpCodes.Ldelem_U1,
            ElementType.I2 => CilOpCodes.Ldelem_I2,
            ElementType.Char or ElementType.U2 => CilOpCodes.Ldelem_U2,
            ElementType.I4 => CilOpCodes.Ldelem_I4,
            ElementType.U4 => CilOpCodes.Ldelem_U4,
            ElementType.I8 or ElementType.U8 => CilOpCodes.Ldelem_I8,
            ElementType.I or ElementType.U => CilOpCodes.Ldelem_I,
            ElementType.R4 => CilOpCodes.Ldelem_R4,
            ElementType.R8 => CilOpCodes.Ldelem_R8,
            _ => (CilOpCode?)null
        }) : null;
        if (primitive.HasValue) instructions.Add(primitive.Value);
        else instructions.Add(store ? CilOpCodes.Stelem : CilOpCodes.Ldelem, type.ToTypeDefOrRef());
    }

    public static void InjectHelpersType(ApplicationAnalysisContext appContext)
    {
        var helpersType = appContext.InjectTypeIntoAllAssemblies(
            HelpersNamespace,
            HelpersTypeName,
            null,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed);

        helpersType.InjectMethodToAllAssemblies(
            NoteIssueMethodName,
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemStringType]);
    }

    public static void GenerateIl(MethodAnalysisContext context, MethodDefinition definition)
    {
        var assembly = context.DeclaringType!.DeclaringAssembly;
        var module = definition.DeclaringModule!;
        var factory = module.CorLibTypeFactory;

        var noteIssueContext = assembly
            .GetTypeByFullName($"{HelpersNamespace}.{HelpersTypeName}")?.Methods.FirstOrDefault(m => m.Name == NoteIssueMethodName);

        var writeLine = noteIssueContext != null
            ? noteIssueContext.ToMethodDescriptor()
            : factory.CorLibScope
                .CreateTypeReference("System", "Console")
                .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(factory.Void, [factory.String]));

        // Change branch targets to instructions
        foreach (var instruction in context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands.Count > 0 && instruction.Operands[0] is Block target)
            {
                if (target.Instructions.Count > 0)
                    instruction.SetOperand(0, target.Instructions[0]);
            }
        }

        var body = new CilMethodBody()
        {
            InitializeLocals = true, // Without this ILSpy does: CompilerServices.Unsafe.SkipInit(out object obj);
            ComputeMaxStackOnBuild = false // Checked after all branch fixups; incomplete bodies remain explicit diagnostics.
        };

        definition.CilMethodBody = body;

        // Make sure context.Locals actually has all locals (idk why it doesn't sometimes)
        foreach (var operand in context.ControlFlowGraph.Instructions.SelectMany(i => i.Operands))
        {
            LocalVariable? local = null;

            if (operand is FieldReference field)
                local = field.Local;

            if (operand is LocalVariable local2)
                local = local2;

            if (operand is MemoryOperand memory && memory.Base is LocalVariable local3)
                local = local3;

            var elementOperand = operand is AddressOf { Target: ArrayAccess elementAddress } ? elementAddress : operand;

            if (elementOperand is ArrayAccess arrayAccess)
            {
                local = arrayAccess.Array;

                if (arrayAccess.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is ArrayLength arrayLength)
                local = arrayLength.Array;

            if (operand is AddressOf { Target: LocalVariable addressed })
                local = addressed;

            if (operand is AddressOf { Target: FieldReference addressedField } && addressedField.RequiresReceiver)
                local = addressedField.Local;

            if (local != null && !context.Locals.Contains(local))
                context.Locals.Add(local);
        }

        // Map ISIL locals to IL
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            TypeSignature ilType;

            // Use object if type couldn't be determined, or if it's void, which no locals sig can hold
            if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType)
                ilType = local.Type.ToTypeSignature();
            else
                ilType = module.CorLibTypeFactory.Object;

            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        /* foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            body.Instructions.Add(CilOpCodes.Ldstr, instruction.ToString());
            body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!));
        }
        body.Instructions.Add(CilOpCodes.Ldstr, "-------------------------------------------------------------------------");
        body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!)); */

        // Generate IL
        Dictionary<Instruction, List<CilInstruction>> instructionMap = [];
        Dictionary<Block, CilInstruction> blockEntryMap = [];
        List<(CilInstruction BranchInstruction, Block TargetBlock)> pendingBlockBranchFixups = [];

        // CFG/BFS execution order is not necessarily the block emission order.
        // Identify calls absorbed by native allocation->CIL newobj BEFORE any
        // block is emitted, otherwise a ctor emitted earlier survives twice.
        var absorbedConstructors = new HashSet<Instruction>();
        foreach(var allocation in context.ControlFlowGraph.Instructions.Where(i=>i.OpCode==OpCode.Newobj))
        {
            if(allocation.Operands is not [_,TypeAnalysisContext allocatedType]
                || FindConstructorCall(context,allocation) is not {Operands:[MethodAnalysisContext ctor,_,..]} call
                || Cpp2IL.Core.Analysis.TrivialConstructorRecovery.BindConstructorOwner(ctor,allocatedType)==null) continue;
            if(!absorbedConstructors.Add(call))
                throw new DecompilerException("ambiguous constructor allocation binding");
        }

        foreach (var block in context.ControlFlowGraph!.Blocks)
        {
            if (block == context.ControlFlowGraph.EntryBlock || block == context.ControlFlowGraph.ExitBlock)
                continue;

            if (block.Instructions.Count == 0)
                continue;

            foreach (var instruction in block.Instructions)
            {
                var generated = absorbedConstructors.Contains(instruction)
                    ? new List<CilInstruction> { definition.CilMethodBody!.Instructions.Add(CilOpCodes.Nop) }
                    : GenerateInstructions(instruction, context, definition, locals, writeLine);
                instructionMap.Add(instruction, generated);

                if (!blockEntryMap.ContainsKey(block) && generated.Count > 0)
                    blockEntryMap[block] = generated[0];
            }

            var lastInstruction = block.Instructions.Last();
            
            if (lastInstruction.OpCode == OpCode.ConditionalJump)
            {
                var trueTarget = TryResolveJumpTargetBlock(lastInstruction, context.ControlFlowGraph);
                var falseSuccessor = block.Successors.FirstOrDefault(s => s != trueTarget && s != context.ControlFlowGraph.ExitBlock);
                if (falseSuccessor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, falseSuccessor));
            }

            else if (lastInstruction.OpCode != OpCode.Jump && lastInstruction.OpCode != OpCode.Return && lastInstruction.OpCode != OpCode.IndirectJump)
            {
                var successor = block.Successors.FirstOrDefault(s => s != context.ControlFlowGraph.ExitBlock);
                if (successor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, successor));
            }
        }
        // Set IL branch targets
        foreach (var kvp in instructionMap)
        {
            var instruction = kvp.Key;
            var il = kvp.Value;

            if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump)
            {
                var ilBranch = il.First(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Brtrue);

                if (instruction.Operands[0] is Block targetBlock)
                {
                    context.AddWarning($"Branch target block not in cfg: {instruction} ({targetBlock})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                var target = (Instruction)instruction.Operands[0];

                if (!instructionMap.ContainsKey(target))
                {
                    context.AddWarning($"Branch target not in ISIL to IL map: {instruction} --- {target}");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                ilBranch.Operand = new CilInstructionLabel(instructionMap[target][0]);
            }
        }
        
        foreach (var (branchInstruction, targetBlock) in pendingBlockBranchFixups)
        {
            var target = ResolveBlockEntryInstruction(targetBlock, blockEntryMap);
            if (target == null)
            {
                context.AddWarning($"Unable to resolve branch target block: {targetBlock}");
                branchInstruction.OpCode = CilOpCodes.Nop;
                branchInstruction.Operand = null;
                continue;
            }

            branchInstruction.Operand = new CilInstructionLabel(target);
        }

        // Add analysis warnings
        var instructions = body.Instructions;
        foreach (var warning in context.AnalysisWarnings)
        {
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }

        // DLL_IL_RECOVERY must emit a valid header for balanced recovered CIL.
        // Keep incomplete bodies diagnostic rather than suppressing their error
        // or preventing unrelated methods from being recovered.
        if (!TryFinalizeMaxStack(body))
        {
            const string warning = "CIL evaluation stack is unbalanced; body is not compile-verified.";
            context.AddWarning(warning);
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }
    }

    internal static bool TryFinalizeMaxStack(CilMethodBody body)
    {
        try
        {
            var maximum = body.ComputeMaxStack();
            body.MaxStack = maximum;
            return true;
        }
        catch (StackImbalanceException)
        {
            return false;
        }
    }

    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";
    
    private static Block? TryResolveJumpTargetBlock(Instruction jumpInstruction, ISILControlFlowGraph cfg)
    {
        if (jumpInstruction.Operands.Count == 0)
            return null;

        if (jumpInstruction.Operands[0] is Block targetBlock)
            return targetBlock;

        if (jumpInstruction.Operands[0] is Instruction targetInstruction)
            return cfg.FindBlockByInstruction(targetInstruction);

        return null;
    }

    private static CilInstruction? ResolveBlockEntryInstruction(Block block,
        Dictionary<Block, CilInstruction> blockEntryMap, HashSet<Block>? visited = null)
    {
        if (blockEntryMap.TryGetValue(block, out var target))
            return target;

        visited ??= [];
        if (!visited.Add(block))
            return null;

        foreach (var successor in block.Successors)
        {
            var resolved = ResolveBlockEntryInstruction(successor, blockEntryMap, visited);
            if (resolved != null)
                return resolved;
        }
        return null;
    }

    private static List<CilInstruction> GenerateInstructions(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var body = method.CilMethodBody!;
        BindParameterIdentities(context);
        var instructions = body.Instructions;
        var currentCount = instructions.Count;
        var startIndex = instructions.Count;

        var module = method.DeclaringModule!;

        switch (instruction.OpCode)
        {
            case OpCode.Invalid:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Invalid instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.NotImplemented:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Not implemented instruction: {instruction.Operands[0]}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Interrupt:
            case OpCode.Nop:
                instructions.Add(CilOpCodes.Nop);
                break;

            case OpCode.NumericConvert:
                if (instruction.Operands is not [_, TypeAnalysisContext numericTarget, TypeAnalysisContext numericSource, var numericValue])
                    throw new DecompilerException("Malformed numeric conversion contract");
                LoadOperand(numericValue, method, locals, writeLine, numericSource);
                if (numericSource.FullName is "System.UInt32" or "System.UInt64"
                    && numericTarget.FullName is "System.Single" or "System.Double")
                    instructions.Add(CilOpCodes.Conv_R_Un);
                instructions.Add(numericTarget.FullName switch
                {
                    "System.SByte" => CilOpCodes.Conv_I1,
                    "System.Byte" => CilOpCodes.Conv_U1,
                    "System.Int16" => CilOpCodes.Conv_I2,
                    "System.UInt16" => CilOpCodes.Conv_U2,
                    "System.Int32" => CilOpCodes.Conv_I4,
                    "System.UInt32" => CilOpCodes.Conv_U4,
                    "System.Int64" => CilOpCodes.Conv_I8,
                    "System.UInt64" => CilOpCodes.Conv_U8,
                    "System.Single" => CilOpCodes.Conv_R4,
                    "System.Double" => CilOpCodes.Conv_R8,
                    _ => throw new DecompilerException("Unsupported numeric conversion target")
                });
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.LoadVirtualFunction:
                if (instruction.Operands is not [LocalVariable { Type.FullName: "System.IntPtr" },
                    MethodAnalysisContext { IsVirtual: true, IsStatic: false } virtualTarget, LocalVariable receiver])
                    throw new DecompilerException("Invalid proven virtual function load");
                LoadLocal(receiver, method, locals);
                instructions.Add(CilOpCodes.Ldvirtftn, virtualTarget.ToMethodDescriptor());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Move:
                // Initialize the actual local, not a scratch struct followed
                // by a copy. Both are CLI initobj at this exact program point;
                // keep .locals init and all nonlocal destination handling.
                if (instruction.Operands is [LocalVariable initializedLocal, DefaultStructValue defaultValue]
                    && ReferenceEquals(initializedLocal.Type, defaultValue.Type) && defaultValue.Type.IsValueType
                    && !initializedLocal.IsThis && ParameterFor(initializedLocal, method) == null
                    && locals.TryGetValue(initializedLocal, out var initializedStorage))
                {
                    instructions.Add(CilOpCodes.Ldloca, initializedStorage);
                    instructions.Add(CilOpCodes.Initobj, defaultValue.Type.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }
                if (instruction.Operands[1] is MemoryOperand { Base: LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { } referent } }, Index: null, Scale: 0, Addend: 0 }
                    && instruction.NativeReadSize > 0
                    && instruction.NativeReadSize != (referent.IsValueType ? TypeSizes.UnboxedSize(referent, context.AppContext.Binary.PointerSizeBytes) : context.AppContext.Binary.PointerSizeBytes))
                    throw new DecompilerException("Unresolved partial managed-byref load");
                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    if (!field.Field.IsStatic)
                        LoadFieldReceiver(field, method, locals);

                    LoadOperand(instruction.Operands[1], method, locals, writeLine, field.Field.FieldType);
                    instructions.Add(field.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadLocal(target.Array, method, locals);
                    LoadArrayIndex(target.Index, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored);
                    EmitArrayElement(instructions, stored.ToTypeSignature(), true);
                    break;
                }

                LoadOperand(instruction.Operands[1], method, locals, writeLine, DestinationType(instruction.Operands[0]));
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewArr:
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    LoadOperand(length, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newarr, newArrayElement.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewVirtualDelegate:
                if (instruction.Operands is not [LocalVariable { Type.IsDelegate: true },
                    MethodAnalysisContext { Name: ".ctor", IsStatic: false, DeclaringType.IsDelegate: true } delegateConstructor,
                    MethodAnalysisContext { IsVirtual: true, IsStatic: false } delegateTarget, LocalVariable delegateReceiver]
                    || delegateConstructor.Parameters.Count != 2
                    || delegateConstructor.Parameters[0].ParameterType.FullName != "System.Object"
                    || delegateConstructor.Parameters[1].ParameterType.FullName != "System.IntPtr")
                    throw new DecompilerException("Invalid proven virtual delegate creation");
                // A future pointer local must NEVER feed the early Newobj fusion.
                // This standard contiguous CIL pattern also round-trips through ILSpy.
                LoadLocal(delegateReceiver, method, locals);
                instructions.Add(CilOpCodes.Dup);
                instructions.Add(CilOpCodes.Ldvirtftn, delegateTarget.ToMethodDescriptor());
                instructions.Add(CilOpCodes.Newobj, delegateConstructor.ToMethodDescriptor());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                if (FindConstructorCall(context, instruction) is { Operands: [MethodAnalysisContext constructor, _, ..] } constructorCall)
                {
                    if (instruction.Operands is not [_, TypeAnalysisContext allocationType]
                        || Cpp2IL.Core.Analysis.TrivialConstructorRecovery.BindConstructorOwner(constructor, allocationType) is not { } boundConstructor)
                        throw new DecompilerException("Constructor owner does not match the native allocation type");
                    constructor = boundConstructor;
                    constructorCall.SetOperand(0, constructor);
                    // Operands run [ctor, newObject, arguments..., methodInfo], so take only as many as
                    // the constructor declares (i.e. drop methodInfo)
                    var constructorArgs = constructorCall.Operands.Skip(ConstructorReceiverIndex(constructorCall) + 1).Take(constructor.Parameters.Count).ToList();
                    for (var i = 0; i < constructorArgs.Count; i++)
                        LoadOperand(constructorArgs[i], method, locals, writeLine, constructor.Parameters[i].ParameterType);

                    instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);

                    constructorCall.OpCode = OpCode.Nop;
                    constructorCall.SetOperands();
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    instructions.Add(CilOpCodes.Newobj, parameterlessCtor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldnull);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, TypeAnalysisContext boxedType, var boxedValue])
                {
                    // il2cpp_value_box takes the value by address, but IL boxes it by value
                    LoadOperand(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue, method, locals, writeLine, boxedType);
                    instructions.Add(CilOpCodes.Box, boxedType.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.IsInst:
                if (instruction.Operands is not [_, TypeAnalysisContext testedType, var testedValue])
                    throw new DecompilerException("Unresolved IsInst operands");
                LoadOperand(testedValue, method, locals, writeLine, context.AppContext.SystemTypes.SystemObjectType);
                instructions.Add(CilOpCodes.Isinst, testedType.ToTypeSignature().ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.CastClass:
                if (instruction.Operands is not [_, TypeAnalysisContext castType, var castValue]
                    || castType is RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
                    || castType.IsValueType)
                    throw new DecompilerException("Unresolved or non-reference CastClass operands");
                LoadOperand(castValue, method, locals, writeLine, context.AppContext.SystemTypes.SystemObjectType);
                instructions.Add(CilOpCodes.Castclass, castType.ToTypeSignature().ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.UnboxAny:
                if (instruction.Operands is not [_, TypeAnalysisContext valueType, var boxedSource]
                    || valueType is RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                        or RuntimeFieldInfoAnalysisContext or ByRefTypeAnalysisContext)
                    throw new DecompilerException("Unresolved UnboxAny operands");
                LoadOperand(boxedSource,method,locals,writeLine,context.AppContext.SystemTypes.SystemObjectType);
                instructions.Add(CilOpCodes.Unbox_Any,valueType.ToTypeSignature().ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0],method,locals,writeLine);
                break;

            case OpCode.ArrayNullCheck:
                if(instruction.Operands is not [LocalVariable {Type:SzArrayTypeAnalysisContext} checkedArray])
                    throw new DecompilerException("Managed array null-check type is unproven");
                LoadOperand(checkedArray,method,locals,writeLine);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Pop);
                break;

            case OpCode.Unbox:
                if (instruction.Operands is not [_, TypeAnalysisContext unboxedType, var boxedObject]
                    || !unboxedType.IsValueType || unboxedType.HasAnyGenericParameters()
                    || unboxedType is not GenericInstanceTypeAnalysisContext && unboxedType.GenericParameters.Count > 0)
                    throw new DecompilerException("Unresolved checked Unbox operands");
                LoadOperand(boxedObject, method, locals, writeLine, context.AppContext.SystemTypes.SystemObjectType);
                var unboxSignature = unboxedType.FullName switch
                {
                    "System.Boolean" => method.DeclaringModule!.CorLibTypeFactory.Boolean,
                    "System.Byte" => method.DeclaringModule!.CorLibTypeFactory.Byte,
                    "System.SByte" => method.DeclaringModule!.CorLibTypeFactory.SByte,
                    "System.Char" => method.DeclaringModule!.CorLibTypeFactory.Char,
                    "System.Int16" => method.DeclaringModule!.CorLibTypeFactory.Int16,
                    "System.UInt16" => method.DeclaringModule!.CorLibTypeFactory.UInt16,
                    "System.Int32" => method.DeclaringModule!.CorLibTypeFactory.Int32,
                    "System.UInt32" => method.DeclaringModule!.CorLibTypeFactory.UInt32,
                    "System.Int64" => method.DeclaringModule!.CorLibTypeFactory.Int64,
                    "System.UInt64" => method.DeclaringModule!.CorLibTypeFactory.UInt64,
                    "System.Single" => method.DeclaringModule!.CorLibTypeFactory.Single,
                    "System.Double" => method.DeclaringModule!.CorLibTypeFactory.Double,
                    "System.IntPtr" => method.DeclaringModule!.CorLibTypeFactory.IntPtr,
                    "System.UIntPtr" => method.DeclaringModule!.CorLibTypeFactory.UIntPtr,
                    _ => unboxedType.ToTypeSignature()
                };
                instructions.Add(CilOpCodes.Unbox, unboxSignature.ToTypeDefOrRef());
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Throw:
                if (instruction.Operands is [TypeAnalysisContext exceptionType]
                    && exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0) is { } exceptionCtor)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference])
                    LoadOperand(instruction.Operands[0], method, locals, writeLine); // an already-constructed exception
                else
                    instructions.Add(CilOpCodes.Ldnull);

                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.Phi:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Phi opcodes should not exist at this point in decompilation ({instruction})"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Call:
            case OpCode.CallVoid:
                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    if (instruction.Operands[0] is Immediate targetAddress)
                        instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                    else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }

                var importedMethod = targetMethod.ToMethodDescriptor();

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;

                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    if ((instruction.Operands.Count - 1) >= thisParamIndex)
                        LoadOperand(instruction.Operands[thisParamIndex], method, locals, writeLine, targetMethod.DeclaringType);
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);
                // A call whose target was only identified after lifting still carries the operands the
                // unknown-callee convention gave it, which may be fewer than the method actually takes.
                // The stack still has to match the signature, so anything missing gets a placeholder.
                var availableArgs = instruction.Operands.Count - callParamIndex;
                for (var i = 0; i < targetMethod.Parameters.Count; i++)
                {
                    var parameterType = targetMethod.Parameters[i].ParameterType;

                    if (i < availableArgs)
                        LoadOperand(instruction.Operands[callParamIndex + i], method, locals, writeLine, parameterType);
                    else
                        PushDefaultOf(parameterType, instructions);
                }

                if(instruction.NativeNullCheckedCall && (targetMethod.IsStatic || targetMethod.IsVirtual
                    || targetMethod.Name.StartsWith(".",System.StringComparison.Ordinal) || targetMethod.DeclaringType?.IsValueType!=false))
                    throw new DecompilerException("Proven null-checked direct call contract changed");
                instructions.Add(instruction.NativeVirtualDispatch || instruction.NativeNullCheckedCall ? CilOpCodes.Callvirt : CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
                    else
                        instructions.Add(CilOpCodes.Pop);
                }

                break;

            case OpCode.IndirectCall:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect call: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Return:
                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                        LoadOperand(instruction.Operands[0], method, locals, writeLine, context.ReturnType);
                    else
                        instructions.Add(CilOpCodes.Ldnull); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel());
                break;

            case OpCode.IndirectJump:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect jump: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                // An unresolved tail transfer is terminal in the native CFG.
                // Falling through here creates malformed CIL (especially after
                // guard removal). Keep it explicitly diagnostic, never invent
                // a successful return or execution of the next native block.
                var unsupportedTransfer = method.DeclaringModule!.CorLibTypeFactory.CorLibScope
                    .CreateTypeReference("System", "NotSupportedException")
                    .CreateMemberReference(".ctor", MethodSignature.CreateInstance(
                        method.DeclaringModule.CorLibTypeFactory.Void,
                        [method.DeclaringModule.CorLibTypeFactory.String]));
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unresolved native indirect tail transfer"));
                instructions.Add(CilOpCodes.Newobj, unsupportedTransfer);
                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.ShiftStack:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Stack shift: {instruction} (stack analysis should have removed these)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:

            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:

            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:
            case OpCode.ShiftRightUnsigned:

            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
                // klass pointer read => GetType
                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitExactTypeComparison(instruction, method, locals, writeLine))
                    break;

                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitScalarStructComparison(instruction, method, locals, writeLine))
                    break;

                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess
                    or OpCode.CheckGreater or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                    && instruction.Operands.Skip(1).Any(o => DestinationType(o) is { IsValueType: true } t
                        && !TypeSizes.IsScalarValueType(t) && !t.HasAnyGenericParameters()))
                    throw new DecompilerException("Unresolved native aggregate comparison; scalar payload/getter proof required");

                // Float arithmetic on a promoted integer operand needs an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatArithmeticConversion(instruction);
                var bitwiseType = instruction.OpCode is OpCode.And or OpCode.Or or OpCode.Xor
                    && DestinationType(instruction.Operands[0]) is { FullName: "System.Int32" or "System.UInt32" } resultType
                    ? resultType : null;
                var integralArithmeticType = instruction.OpCode is OpCode.Add or OpCode.Subtract
                    or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                    && DestinationType(instruction.Operands[0]) is { FullName: "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" } integralResult
                    ? integralResult : null;
                var comparison = instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    or OpCode.CheckLess or OpCode.CheckGreater or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual;
                var comparisonType=comparison?ComparisonStackType(instruction):null;
                var nativeArithmeticType=NativeIntegerArithmeticType(instruction,context);

                if(nativeArithmeticType!=null)
                    LoadNativeArithmeticOperand(instruction,instruction.Operands[1],context,method,locals,writeLine);
                else LoadOperandCore(instruction.Operands[1], method, locals, writeLine,
                    comparison ? comparisonType ?? DestinationType(instruction.Operands[2]) : nativeArithmeticType ?? integralArithmeticType ?? bitwiseType,
                    coerceIntegral:comparison || nativeArithmeticType!=null);
                if (EnumArithmeticConversion(instruction.Operands[1], integralArithmeticType ?? bitwiseType) is { } enumConv1)
                    instructions.Add(enumConv1);
                if (floatConversion is { } conv1)
                    instructions.Add(conv1);
                if(nativeArithmeticType!=null)
                    LoadNativeArithmeticOperand(instruction,instruction.Operands[2],context,method,locals,writeLine);
                else LoadOperandCore(instruction.Operands[2], method, locals, writeLine,
                    comparison ? comparisonType ?? DestinationType(instruction.Operands[1]) : nativeArithmeticType ?? integralArithmeticType ?? bitwiseType,
                    coerceIntegral:comparison || nativeArithmeticType!=null);
                if (EnumArithmeticConversion(instruction.Operands[2], integralArithmeticType ?? bitwiseType) is { } enumConv2)
                    instructions.Add(enumConv2);
                if (floatConversion is { } conv2)
                    instructions.Add(conv2);

                switch (instruction.OpCode)
                {
                    case OpCode.CheckEqual: instructions.Add(CilOpCodes.Ceq); break;
                    case OpCode.CheckGreater: instructions.Add(instruction.UnsignedComparison ? CilOpCodes.Cgt_Un : CilOpCodes.Cgt); break;
                    case OpCode.CheckLess: instructions.Add(instruction.UnsignedComparison ? CilOpCodes.Clt_Un : CilOpCodes.Clt); break;

                    // a != b  ==  (a == b) == 0
                    case OpCode.CheckNotEqual:
                        instructions.Add(CilOpCodes.Ceq);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a >= b  ==  !(a < b)
                    case OpCode.CheckGreaterOrEqual:
                        instructions.Add(instruction.UnsignedComparison ? CilOpCodes.Clt_Un : CilOpCodes.Clt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a <= b  ==  !(a > b)
                    case OpCode.CheckLessOrEqual:
                        instructions.Add(instruction.UnsignedComparison ? CilOpCodes.Cgt_Un : CilOpCodes.Cgt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;

                    case OpCode.Add: instructions.Add(CilOpCodes.Add); break;
                    case OpCode.Subtract: instructions.Add(CilOpCodes.Sub); break;
                    case OpCode.Multiply: instructions.Add(CilOpCodes.Mul); break;
                    case OpCode.Divide: instructions.Add(CilOpCodes.Div); break;
                    case OpCode.Modulo: instructions.Add(CilOpCodes.Rem); break;

                    case OpCode.ShiftLeft: instructions.Add(CilOpCodes.Shl); break;
                    case OpCode.ShiftRight: instructions.Add(CilOpCodes.Shr); break;
                    case OpCode.ShiftRightUnsigned: instructions.Add(CilOpCodes.Shr_Un); break;

                    case OpCode.And: instructions.Add(CilOpCodes.And); break;
                    case OpCode.Or: instructions.Add(CilOpCodes.Or); break;
                    case OpCode.Xor: instructions.Add(CilOpCodes.Xor); break;
                }

                if(nativeArithmeticType!=null && IntegralLoadConversion(
                    new LocalVariable("nativeResult",new Register(null,"NATIVE_RESULT"),nativeArithmeticType),
                    DestinationType(instruction.Operands[0])) is {} resultConversion)
                    instructions.Add(resultConversion);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Absolute:
                if(instruction.NativeFloatingPointSize is not (4 or 8)
                    || context.DeclaringType?.FullName=="System.Math" && context.Name=="Abs")
                    throw new DecompilerException("Native floating absolute requires a nonrecursive runtime intrinsic reference");
                var absoluteType=instruction.NativeFloatingPointSize==4?context.AppContext.SystemTypes.SystemSingleType:
                    context.AppContext.SystemTypes.SystemDoubleType;
                var absoluteSource=instruction.Operands[1];
                if(DestinationType(instruction.Operands[0])?.FullName!=absoluteType.FullName
                    || DestinationType(absoluteSource)?.FullName!=absoluteType.FullName
                        && !(instruction.NativeFloatingPointSize==4 && absoluteSource is FloatLiteral)
                        && !(instruction.NativeFloatingPointSize==8 && absoluteSource is DoubleLiteral))
                    throw new DecompilerException("Native floating absolute source width/type differs");
                var absoluteModule=method.DeclaringModule!;
                var absoluteSignature=instruction.NativeFloatingPointSize==4?absoluteModule.CorLibTypeFactory.Single:
                    absoluteModule.CorLibTypeFactory.Double;
                var absolute=absoluteModule.CorLibTypeFactory.CorLibScope.CreateTypeReference("System","Math")
                    .CreateMemberReference("Abs",MethodSignature.CreateStatic(absoluteSignature,[absoluteSignature]));
                LoadOperand(instruction.Operands[1],method,locals,writeLine,absoluteType);
                instructions.Add(CilOpCodes.Call,absolute);
                StoreToOperand(instruction.Operands[0],method,locals,writeLine);
                break;

            case OpCode.Not:
            case OpCode.Negate:
                var nativeNegateType=instruction.OpCode==OpCode.Negate && instruction.NativeArithmeticSize is 4 or 8
                    && IntegralStackWidth(DestinationType(instruction.Operands[1])?.FullName)!=0
                    && IntegralStackWidth(DestinationType(instruction.Operands[0])?.FullName)!=0
                    ? instruction.NativeArithmeticSize==4?context.AppContext.SystemTypes.SystemUInt32Type
                        :context.AppContext.SystemTypes.SystemUInt64Type : null;
                LoadOperand(instruction.Operands[1], method, locals, writeLine,nativeNegateType);

                if (instruction.OpCode == OpCode.Negate)
                    instructions.Add(CilOpCodes.Neg);
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                }
                else
                    instructions.Add(CilOpCodes.Not);

                if(nativeNegateType!=null && IntegralLoadConversion(
                    new LocalVariable("nativeNegateResult",new Register(null,"NATIVE_NEGATE_RESULT"),nativeNegateType),
                    DestinationType(instruction.Operands[0])) is {} negateConversion)instructions.Add(negateConversion);
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;
        }

        return instructions.ToList().GetRange(startIndex, instructions.Count - startIndex); // Return added IL
    }
    
    private static int ConstructorReceiverIndex(Instruction constructorCall) => constructorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    // Try find the follow up CallVoid for a constructor, after a Newobj.
    internal static Instruction? FindConstructorCall(MethodAnalysisContext context, Instruction newobj)
    {
        var newObject = newobj.Operands[0];

        // A flattened BFS list interleaves mutually exclusive branches, and
        // post-SSA locals may be reused. Follow actual successor paths while
        // this allocation's value is live; never cross a redefinition.
        var graph=context.ControlFlowGraph!;
        var origin=graph.Blocks.SingleOrDefault(b=>b.Instructions.Contains(newobj));
        if(origin==null)return null;
        var pending=new Queue<(Block Block,int Start)>();
        var visited=new HashSet<(Block,int)>();
        var matches=new HashSet<Instruction>();
        pending.Enqueue((origin,origin.Instructions.IndexOf(newobj)+1));
        while(pending.Count>0)
        {
            var (block,start)=pending.Dequeue();
            if(!visited.Add((block,start)))continue;
            var stopped=false;
            for(var i=start;i<block.Instructions.Count;i++)
            {
                var candidate=block.Instructions[i];
                if(ReferenceEquals(candidate.Destination,newObject)){stopped=true;break;}
                if(candidate is not {OpCode:OpCode.Call or OpCode.CallVoid,Operands:[MethodAnalysisContext {Name:".ctor"},..]})continue;
                var receiver=ConstructorReceiverIndex(candidate);
                if(candidate.Operands.Count<=receiver || !ReferenceEquals(candidate.Operands[receiver],newObject))continue;
                matches.Add(candidate);stopped=true;break;
            }
            if(!stopped)foreach(var successor in block.Successors)pending.Enqueue((successor,0));
        }
        return matches.Count==1?matches.Single():null;
    }

    internal static CilOpCode? EnumArithmeticConversion(IOperand operand, TypeAnalysisContext? expected)
    {
        // The native arithmetic has already been typed as a primitive integer.
        // Preserve the enum declaration, but make its integer use explicit in IL
        // so a C# decompiler cannot emit the invalid `int - enum` expression.
        // These conversions are evaluation-stack bit-pattern identities only:
        // never infer an enum width or widen/narrow it to fit another operand.
        if (DestinationType(operand) is not { IsEnumType: true, EnumUnderlyingType: { } underlying })
            return null;
        return (underlying.FullName, expected?.FullName) switch
        {
            ("System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32",
                "System.Int32" or "System.UInt32") => CilOpCodes.Conv_I4,
            ("System.Int64" or "System.UInt64", "System.Int64" or "System.UInt64") => CilOpCodes.Conv_I8,
            _ => null,
        };
    }

    private static CilOpCode? FloatArithmeticConversion(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo))
            return null;

        return (instruction.Operands[0] as LocalVariable)?.Type?.FullName switch
        {
            "System.Single" => CilOpCodes.Conv_R4,
            "System.Double" => CilOpCodes.Conv_R8,
            _ => null,
        };
    }

    // CIL evaluation-stack widths must agree with the exact managed field,
    // element, parameter or result contract. Never coerce references, pointer
    // carriers, bools, floats or unknown storage into integers to silence IL.
    static int IntegralStackWidth(string? type)=>type switch
    {
        "System.SByte" or "System.Byte" or "System.Int16" or "System.UInt16"
            or "System.Char" or "System.Int32" or "System.UInt32"=>4,
        "System.Int64" or "System.UInt64"=>8,_=>0,
    };

    static void LoadNativeArithmeticOperand(Instruction instruction,IOperand value,MethodAnalysisContext context,
        MethodDefinition method,Dictionary<LocalVariable,CilLocalVariable> locals,IMethodDescriptor writeLine)
    {
        var types=context.AppContext.SystemTypes;
        if(instruction.OpCode==OpCode.Multiply && instruction.NativeArithmeticSize==8 && instruction.NativeMultiplyInputSize==4)
        {
            var narrow=instruction.NativeMultiplySigned?types.SystemInt32Type:types.SystemUInt32Type;
            LoadOperand(value,method,locals,writeLine,narrow);
            // Native long multiply reads W bits, then sign/zero extends each
            // input independently BEFORE the full-width product.
            method.CilMethodBody!.Instructions.Add(instruction.NativeMultiplySigned?CilOpCodes.Conv_I4:CilOpCodes.Conv_U4);
            method.CilMethodBody.Instructions.Add(instruction.NativeMultiplySigned?CilOpCodes.Conv_I8:CilOpCodes.Conv_U8);
        }
        else LoadOperand(value,method,locals,writeLine,NativeIntegerArithmeticType(instruction,context));
    }

    internal static TypeAnalysisContext? NativeIntegerArithmeticType(Instruction instruction,MethodAnalysisContext context)
    {
        if(instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply)
            || instruction.NativeArithmeticSize is not (4 or 8) || instruction.Operands.Count!=3
            || IntegralStackWidth(DestinationType(instruction.Operands[0])?.FullName)==0)return null;
        foreach(var value in instruction.Operands.Skip(1))
        {
            var type=DestinationType(value);if(type?.IsEnumType==true)type=type.EnumUnderlyingType;
            if(value is not Immediate && IntegralStackWidth(type?.FullName)==0)return null;
        }
        // Only modulo add/sub/mul under an explicit native width. Division,
        // shifts, pointer carriers and floats require their own contracts.
        return instruction.NativeArithmeticSize==8?context.AppContext.SystemTypes.SystemUInt64Type
            :context.AppContext.SystemTypes.SystemUInt32Type;
    }

    internal static TypeAnalysisContext? ComparisonStackType(Instruction instruction)
    {
        var a=DestinationType(instruction.Operands[1]);var b=DestinationType(instruction.Operands[2]);
        if(a?.IsEnumType==true)a=a.EnumUnderlyingType;if(b?.IsEnumType==true)b=b.EnumUnderlyingType;
        // Widen the I4 side; never independently swap/narrow the two stack
        // widths or truncate an I8 index just to compare against an I4 length.
        return (IntegralStackWidth(a?.FullName),IntegralStackWidth(b?.FullName)) switch
        { (8,4)=>a,(4,8)=>b,_=>null };
    }

    internal static CilOpCode? IntegralLoadConversion(IOperand operand,TypeAnalysisContext? expected)
    {
        var source=DestinationType(operand);
        if(source?.IsEnumType==true)source=source.EnumUnderlyingType;
        if(expected?.IsEnumType==true)expected=expected.EnumUnderlyingType;
        var from=IntegralStackWidth(source?.FullName);var to=IntegralStackWidth(expected?.FullName);
        if(from==0 || to==0 || from==to)return null;
        if(to==8)return source!.FullName is "System.Byte" or "System.UInt16" or "System.Char" or "System.UInt32"
            ? CilOpCodes.Conv_U8 : CilOpCodes.Conv_I8;
        return expected!.FullName switch
        {
            "System.SByte"=>CilOpCodes.Conv_I1,"System.Byte"=>CilOpCodes.Conv_U1,
            "System.Int16"=>CilOpCodes.Conv_I2,"System.UInt16" or "System.Char"=>CilOpCodes.Conv_U2,
            "System.UInt32"=>CilOpCodes.Conv_U4,_=>CilOpCodes.Conv_I4,
        };
    }

    private static void LoadArrayIndex(IOperand index,MethodDefinition method,
        Dictionary<LocalVariable,CilLocalVariable> locals,IMethodDescriptor writeLine)
    {
        LoadOperand(index,method,locals,writeLine);
        var type=DestinationType(index);
        // These checked width-preserving conversions cannot overflow on the
        // matching 64-bit image. Unlike unchecked conv.i/u, ILSpy recognizes
        // them as normal C# 7.3 long/ulong array indexes, not void* casts.
        if(type is {AppContext.Binary.PointerSizeBytes:8,FullName:"System.Int64" or "System.UInt64"})
            method.CilMethodBody!.Instructions.Add(type.FullName=="System.UInt64"
                ? CilOpCodes.Conv_Ovf_U_Un : CilOpCodes.Conv_Ovf_I);
    }

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType = null)
        =>LoadOperandCore(operand,method,locals,writeLine,expectedType,true);

    private static void LoadOperandCore(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType,bool coerceIntegral)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number.
        if (expectedType is { IsValueType: false } && IsZeroConstant(operand))
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        // Enum values have the evaluation-stack width of their metadata
        // underlying type, not the width suggested by an unsigned literal.
        var integralType = expectedType is { IsEnumType: true } ? expectedType.EnumUnderlyingType : expectedType;

        switch (operand)
        {
            case Immediate wide when integralType is { FullName: "System.Int64" or "System.UInt64" }:
                // Even zero and one must be I8 for a long field/argument/return.
                instructions.Add(CilOpCodes.Ldc_I8, wide.Value);
                break;
            case Immediate { Value: > int.MaxValue and <= uint.MaxValue } mask
                when integralType is { FullName: "System.Int32" or "System.UInt32" }:
                // An Int32 bitmask such as 0x80000000 is an I4 bit pattern,
                // not an I8 operand merely because its unsigned spelling is positive.
                instructions.Add(CilOpCodes.Ldc_I4, unchecked((int)mask.Value));
                break;
            case Immediate { Value: >= int.MinValue and <= int.MaxValue } immediate:
                instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                break;
            case Immediate immediate:
                instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            case FloatLiteral f:
                instructions.Add(CilOpCodes.Ldc_R4, f.Value);
                break;
            case DefaultStructValue value:
                var initialized=new CilLocalVariable(value.Type.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(initialized);
                instructions.Add(CilOpCodes.Ldloca,initialized);
                instructions.Add(CilOpCodes.Initobj,value.Type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Ldloc,initialized);
                break;
            case DoubleLiteral d:
                instructions.Add(CilOpCodes.Ldc_R8, d.Value);
                break;
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals);
                break;
            case ArrayLength arrayLength:
                LoadLocal(arrayLength.Array, method, locals);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                instructions.Add(CilOpCodes.Ldloca, locals[addressed]);
                break;
            case AddressOf { Target: FieldReference addressedField }:
                if (addressedField.Field.IsStatic)
                    instructions.Add(CilOpCodes.Ldsflda, addressedField.Field.ToFieldDescriptor());
                else
                {
                    LoadFieldReceiver(addressedField, method, locals);
                    instructions.Add(CilOpCodes.Ldflda, addressedField.Field.ToFieldDescriptor());
                }
                break;
            case AddressOf { Target: ArrayAccess elementAddress }:
                LoadLocal(elementAddress.Array, method, locals);
                LoadArrayIndex(elementAddress.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema,
                    ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayAccess arrayAccess:
                LoadLocal(arrayAccess.Array, method, locals);
                LoadArrayIndex(arrayAccess.Index, method, locals, writeLine);
                EmitArrayElement(instructions,
                    ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType.ToTypeSignature(), false);
                break;
            case FieldReference field:
                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Ldsfld, field.Field.ToFieldDescriptor());
                    break;
                }

                LoadFieldReceiver(field, method, locals);
                instructions.Add(CilOpCodes.Ldfld, field.Field.ToFieldDescriptor());
                break;
            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    LoadLocal(local2, method, locals);

                    // A load through a managed pointer (byref) dereferences it to yield the referent.
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } referent })
                        // An unconstrained generic parameter may be a value
                        // type at runtime. ldind.ref would misread its storage.
                        instructions.Add(referent.IsValueType || referent is GenericParameterTypeAnalysisContext
                            ? new CilInstruction(CilOpCodes.Ldobj, referent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Ldind_Ref));
                    break;
                }
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeMethodInfoAnalysisContext runtimeMethod:
                // A delegate constructor takes its target as a native pointer, which is exactly ldftn.
                if (expectedType?.FullName == "System.IntPtr")
                {
                    instructions.Add(CilOpCodes.Ldftn, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeClassTypeAnalysisContext runtimeClass when expectedType?.FullName == "System.RuntimeTypeHandle":
                instructions.Add(CilOpCodes.Ldtoken, runtimeClass.RepresentedType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext:
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case TypeAnalysisContext type:
                if (expectedType?.FullName == "System.RuntimeTypeHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }
                //typeof(T)
                var corLibScope = module.CorLibTypeFactory.CorLibScope;
                var typeFromHandle = corLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        corLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false),
                        [corLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));

                instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, typeFromHandle);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
        if(coerceIntegral && IntegralLoadConversion(operand,expectedType) is {} integralConversion)
            instructions.Add(integralConversion);
    }
    
    private static bool TryEmitExactTypeComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        IOperand typeOperand;
        LocalVariable objLocal;

        if (left is TypeAnalysisContext && IsKlassPointerLoad(right, out var rightLocal))
            (typeOperand, objLocal) = (left, rightLocal);
        else if (right is TypeAnalysisContext && IsKlassPointerLoad(left, out var leftLocal))
            (typeOperand, objLocal) = (right, leftLocal);
        else
            return false;

        var module = method.DeclaringModule!;
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        StoreToOperand(instruction.Operands[0], method, locals, writeLine);
        return true;
    }
    
    private static bool TryEmitScalarStructComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        if (instruction.Operands.Count != 3 || DestinationType(instruction.Operands[1]) is not { IsValueType: true } left
            || DestinationType(instruction.Operands[2]) is not { IsValueType: true } right
            || !TrivialConstructorRecovery.SameType(left, right)
            || NativeScalarStructComparison.Find(left, instruction.NativeComparisonSize) is not { } getter) return false;
        var code = method.CilMethodBody!.Instructions;
        foreach (var operand in instruction.Operands.Skip(1))
        {
            // A fresh, addressable CURRENT value preserves operand evaluation
            // order and needs no private field access or unsafe reinterpretation.
            var scratch = new CilLocalVariable(left.ToTypeSignature());
            method.CilMethodBody.LocalVariables.Add(scratch);
            LoadOperand(operand, method, locals, writeLine);
            code.Add(CilOpCodes.Stloc, scratch);
            code.Add(CilOpCodes.Ldloca, scratch);
            code.Add(CilOpCodes.Call, getter.ToMethodDescriptor());
        }
        code.Add(CilOpCodes.Ceq);
        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            code.Add(CilOpCodes.Ldc_I4_0); code.Add(CilOpCodes.Ceq);
        }
        StoreToOperand(instruction.Operands[0], method, locals, writeLine);
        return true;
    }

    private static bool IsKlassPointerLoad(IOperand operand, out LocalVariable local)
    {
        if (operand is MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type.IsValueType: false } baseLocal })
        {
            local = baseLocal;
            return true;
        }

        local = null!;
        return false;
    }

    private static void PushDefaultOf(TypeAnalysisContext type, CilInstructionCollection instructions)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (!type.IsValueType)
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (type.FullName)
        {
            case "System.Single": instructions.Add(CilOpCodes.Ldc_R4, 0f); break;
            case "System.Double": instructions.Add(CilOpCodes.Ldc_R8, 0d); break;
            case "System.Int64" or "System.UInt64": instructions.Add(CilOpCodes.Ldc_I8, 0L); break;
            default: instructions.Add(CilOpCodes.Ldc_I4_0); break;
        }
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        operand is LocalVariable { Type: { } type } && type == context.AppContext.SystemTypes.SystemBooleanType;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
    
    private static TypeAnalysisContext? DestinationType(IOperand destination) =>
        destination switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            MemoryOperand { Base: LocalVariable { Type: ByRefTypeAnalysisContext reference }, Index: null, Scale: 0, Addend: 0 } => reference.ElementType,
            _ => null
        };

    private static void BindParameterIdentities(MethodAnalysisContext context)
    {
        // The complete ordered incoming set, not display names, identifies
        // parameters. A partial set needs explicit ordinals from CreateAll.
        var incoming=context.ParameterLocals.Where(l=>!l.IsThis && !l.IsMethodInfo).ToArray();
        if(incoming.Length!=context.Parameters.Count)return;
        for(var ordinal=0;ordinal<incoming.Length;ordinal++)
        {
            if(incoming[ordinal].ParameterIndex<0)incoming[ordinal].ParameterIndex=context.Parameters[ordinal].ParameterIndex;
        }
    }

    private static AsmResolver.DotNet.Collections.Parameter? ParameterFor(LocalVariable local,MethodDefinition method)
    {
        if(local.ParameterIndex<0)return null;
        var signatureIndex=local.ParameterIndex+method.Parameters.MethodSignatureIndexBase;
        if(!method.Parameters.ContainsSignatureIndex(signatureIndex))
            throw new DecompilerException("incoming parameter ordinal outside managed signature");
        return method.Parameters.GetBySignatureIndex(signatureIndex);
    }

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = ParameterFor(local,method);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void LoadFieldReceiver(FieldReference field,MethodDefinition method,Dictionary<LocalVariable,CilLocalVariable> locals)
        => LoadFieldReceiver(field,field.Local,method,locals);

    private static void LoadFieldReceiver(FieldReference field,LocalVariable root,MethodDefinition method,Dictionary<LocalVariable,CilLocalVariable> locals)
    {
        if(field.Parent==null)
        {
            if(root.Type?.IsValueType==true && !root.IsThis)
            {
                var parameter=ParameterFor(root,method);
                if(parameter!=null) method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarga,parameter);
                else method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldloca,locals[root]);
            }
            else LoadLocal(root,method,locals);
            return;
        }
        if(field.Parent.Field.IsStatic)
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldsflda,field.Parent.Field.ToFieldDescriptor());
        else
        {
            LoadFieldReceiver(field.Parent,root,method,locals);
            method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldflda,field.Parent.Field.ToFieldDescriptor());
        }
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                instructions.Add(CilOpCodes.Stloc, locals[local]);
                break;

            case FieldReference field:
                var fieldDescriptor = field.Field.ToFieldDescriptor();

                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object.
                var scratch = new CilLocalVariable(fieldDescriptor.Signature!.FieldType);
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                LoadFieldReceiver(field, method, locals);
                instructions.Add(CilOpCodes.Ldloc, scratch);
                instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadLocal(arrayAccess.Array, method, locals);
                LoadArrayIndex(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
                EmitArrayElement(instructions, elementType.ToTypeSignature(), true);
                break;

            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } referent })
                    {
                        var value = new CilLocalVariable(referent.ToTypeSignature());
                        method.CilMethodBody!.LocalVariables.Add(value);
                        instructions.Add(CilOpCodes.Stloc, value);
                        LoadLocal(local2, method, locals);
                        instructions.Add(CilOpCodes.Ldloc, value);
                        // stobj !0 is valid for both generic instantiation
                        // kinds; stind.ref is valid only for known references.
                        instructions.Add(referent.IsValueType || referent is GenericParameterTypeAnalysisContext
                            ? new CilInstruction(CilOpCodes.Stobj, referent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Stind_Ref));
                    }
                    else
                        instructions.Add(CilOpCodes.Stloc, locals[local2]);
                    break;
                }
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unmanaged memory store: {memory}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Store into unknown operand: {operand}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;
        }
    }
}
