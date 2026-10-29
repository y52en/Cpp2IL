using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Reconstitute only complete native constructor templates: an exact proven base
// invocation followed by distinct this-field assignments. Preserve base effects.
public static class InlinedConstructorRecovery
{
    public const string CacheKey = "PureFieldConstructorTemplates";
    public sealed record Assignment(FieldAnalysisContext Field, int Parameter, IOperand? Constant = null)
    { public int NativeWidth {get;init;} }
    public sealed record Argument(int Parameter,IOperand? Constant=null);
    public sealed record Template(MethodAnalysisContext Constructor, IReadOnlyList<Assignment> Assignments,
        MethodAnalysisContext? BaseConstructor = null)
    {
        public IReadOnlyList<Argument>? BaseArguments {get;init;}
    }

    private static List<TypeAnalysisContext>? Hierarchy(TypeAnalysisContext owner)
    {
        var result=new List<TypeAnalysisContext>();var seen=new HashSet<TypeAnalysisContext>();
        for(var current=owner;current!=null;current=current.BaseType)
        {
            if(result.Count>=32 || current.IsValueType || current.HasAnyGenericParameters() || !seen.Add(current))return null;
            result.Add(current);
        }
        return result;
    }

    private static bool OwnsField(TypeAnalysisContext owner,FieldAnalysisContext field)
        => !field.IsStatic && (field.Attributes&System.Reflection.FieldAttributes.Literal)==0
            && Hierarchy(owner) is {} chain && chain.Contains(field.DeclaringType)
            && field.DeclaringType.Fields.Contains(field);

    private static int FieldWidth(FieldAnalysisContext field,int pointerSize)
    {
        var type=field.FieldType;
        if(type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext || type.HasAnyGenericParameters())return 0;
        var scalar=type.IsEnumType?type.EnumUnderlyingType:type;
        return !type.IsValueType?pointerSize:scalar?.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32" or "System.Single"=>4,
            "System.Int64" or "System.UInt64" or "System.Double"=>8,
            "System.IntPtr" or "System.UIntPtr"=>pointerSize,_=>0,
        };
    }

    private static bool DirectBase(TypeAnalysisContext owner,MethodAnalysisContext target)
        => !owner.IsValueType && !owner.HasAnyGenericParameters() && owner.BaseType is {} parent
            && !parent.HasAnyGenericParameters() && target.Name==".ctor" && !target.IsStatic
            && !target.IsVirtual && target.IsVoid && target.Parameters.Count<=8 && target.GenericParameters.Count==0
            && (TrivialConstructorRecovery.SameType(parent,target.DeclaringType)
                // Complete Ghidra1564: an optimized child native constructor
                // calls Object.ctor and writes an inherited field directly.
                // Match THAT complete body, never infer skipped parent effects
                // from metadata or invent a call to an arbitrary ancestor.
                || ReferenceEquals(target.DeclaringType,owner.AppContext.SystemTypes.SystemObjectType)
                    && target.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey) is {IsNoOp:true}
                    && Hierarchy(owner) is {} chain && chain.Contains(target.DeclaringType));

    public static Template? Extract(MethodAnalysisContext ctor)
    {
        Trace(ctor, "constructor template input");
        if (ctor.Name != ".ctor" || ctor.IsStatic || !ctor.IsVoid || ctor.DeclaringType is not { IsValueType:false } owner
            || owner.BaseType == null || owner.HasAnyGenericParameters()
            || ctor.ControlFlowGraph == null) return null;
        var parameters = ctor.ParameterLocals.Where(l => !l.IsThis && !l.IsMethodInfo).ToList();
        if (parameters.Count != ctor.Parameters.Count) return null;
        if (ctor.ControlFlowGraph.Blocks.Any(b => b.Successors.Count > 1)) return null;
        var visited = new HashSet<Graphs.Block>();
        var block = ctor.ControlFlowGraph.EntryBlock;
        while (block.Successors.Count == 1)
        {
            if (!visited.Add(block)) return null;
            block = block.Successors[0];
        }
        if(owner.BaseType.FullName!="System.Object")
        {
            visited.Add(block);
            if(!ReferenceEquals(block,ctor.ControlFlowGraph.ExitBlock)
                || ctor.ControlFlowGraph.Blocks.Any(b=>!visited.Contains(b)))return null;
        }
        var result = new List<Assignment>();
        var baseCalls = 0;
        MethodAnalysisContext? baseConstructor = null;
        var baseArguments=new List<Argument>();
        var objectBase=owner.BaseType.FullName=="System.Object";
        var returned = false;
        foreach (var instruction in ctor.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
            if(returned)return null;
            if (instruction.OpCode == OpCode.Return && instruction.Operands.Count == 0) { returned = true; continue; }
            if (instruction is { OpCode: OpCode.CallVoid, NativeVirtualDispatch:false,
                Operands: [MethodAnalysisContext parent, LocalVariable { IsThis: true },..] }
                && DirectBase(owner,parent)
                && (objectBase || ctor.ParameterLocals.Any(p=>p.IsThis && ReferenceEquals(p,instruction.Operands[1]))))
            {
                if(++baseCalls>1 || instruction.Operands.Count!=parent.Parameters.Count+2)return null;
                for(var n=0;n<parent.Parameters.Count;n++)
                {
                    var value=instruction.Operands[n+2];var baseParameter=value is LocalVariable baseLocal?parameters.IndexOf(baseLocal):-1;
                    if(baseParameter>=0)
                    {
                        if(!TrivialConstructorRecovery.SameType(ctor.Parameters[baseParameter].ParameterType,parent.Parameters[n].ParameterType))return null;
                        baseArguments.Add(new(baseParameter));
                    }
                    else if(ExactConstant(parent.Parameters[n].ParameterType,value))baseArguments.Add(new(-1,value));
                    else return null;
                }
                baseConstructor=parent;continue;
            }
            if (instruction is not { OpCode: OpCode.Move, Operands: [FieldReference field, var source] }
                || !field.Local.IsThis || field.Parent!=null || !OwnsField(owner,field.Field)
                || !ReferenceEquals(field.Field.DeclaringType,owner)
                    && (field.Offset!=field.Field.Offset || instruction.NativeWriteSize<=0
                        || instruction.NativeWriteSize!=FieldWidth(field.Field,owner.AppContext.Binary.PointerSizeBytes)))
                return null;
            if(!objectBase && (baseCalls!=1 || !ctor.ParameterLocals.Any(p=>p.IsThis && ReferenceEquals(p,field.Local))))return null;
            var parameter = source is LocalVariable local ? parameters.IndexOf(local) : -1;
            if (result.Any(a => a.Field == field.Field)) return null;
            if (parameter >= 0) result.Add(new(field.Field, parameter){NativeWidth=instruction.NativeWriteSize});
            else if (field.Parent == null && ExactConstant(field.Field.FieldType, source))
                result.Add(new(field.Field, -1, source){NativeWidth=instruction.NativeWriteSize});
            else return null;
        }
        if (!returned || result.Count == 0 || !objectBase && baseCalls!=1
            || Enumerable.Range(0,parameters.Count).Any(i => result.All(a => a.Parameter != i)
                && baseArguments.All(a=>a.Parameter!=i))) return null;
        return new(ctor, result.ToArray(),baseConstructor){BaseArguments=baseArguments.ToArray()};
    }

    public static void Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph == null) return;
        Trace(method, "caller before constructor recovery");
        foreach (var allocation in method.ControlFlowGraph.Instructions.ToArray())
            if (allocation is { OpCode: OpCode.Newobj, Operands: [LocalVariable _, TypeAnalysisContext type] }
                && type.GetExtraData<Template[]>(CacheKey) is { Length: > 0 } templates)
                Recover(method, allocation, templates);
    }

    private static void Trace(MethodAnalysisContext method, string stage)
    {
        var requested = System.Environment.GetEnvironmentVariable("CPP2IL_TRACE_CONSTRUCTOR_RVAS");
        if (requested == null || !requested.Split(',').Any(r => string.Equals(r.Trim(),
            method.UnderlyingPointer.ToString("X"), System.StringComparison.OrdinalIgnoreCase))) return;
        System.Console.Error.WriteLine(stage + ": " + method.FullName);
        if (method.ControlFlowGraph == null) return;
        foreach (var block in method.ControlFlowGraph.Blocks)
            System.Console.Error.WriteLine(block + "Successors: " + string.Join(",",block.Successors.Select(s=>s.ID)));
    }

    private static bool RootNoOp(Template template,TypeAnalysisContext owner)
        => template.BaseConstructor is {Name:".ctor",IsStatic:false,Parameters.Count:0} parent
            && ReferenceEquals(parent.DeclaringType,owner.AppContext.SystemTypes.SystemObjectType)
            && parent.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey)
                is {IsNoOp:true};

    private static bool ScalarSetupClass(TypeAnalysisContext owner)
        => Hierarchy(owner) is {} hierarchy && hierarchy.All(type=>
            (type.Attributes&System.Reflection.TypeAttributes.LayoutMask)!=System.Reflection.TypeAttributes.ExplicitLayout
            && !type.Methods.Any(m=>m.Name==".cctor"
                || m.Name=="Finalize" && !ReferenceEquals(type,owner.AppContext.SystemTypes.SystemObjectType)));

    // A constructor whose complete native template only writes zero scalar
    // values leaves a newly allocated, zero-filled object unchanged. This is
    // useful when the original field initialization spans branches: keep EVERY
    // original store and substitute only the proven empty Object-base call.
    // Never use this for reference writes, finalizers, class initializers,
    // volatile/custom-modified fields, overlaps, nonzero constants or effects.
    internal static IOperand[]? ZeroStateArguments(Template template,TypeAnalysisContext owner)
    {
        var ctor=template.Constructor;
        if(!ReferenceEquals(ctor.DeclaringType,owner) || owner.IsValueType || owner.HasAnyGenericParameters()
            || ctor.Name!=".ctor" || ctor.IsStatic || ctor.IsVirtual || !ctor.IsVoid
            || ctor.Parameters.Count is 0 or >8 || ctor.GenericParameters.Count!=0
            || !RootNoOp(template,owner) || !ScalarSetupClass(owner)
            || template.Assignments.Count==0 || (template.BaseArguments?.Count??0)!=0)return null;
        IOperand? Zero(TypeAnalysisContext type)
        {
            var scalar=type.IsEnumType?type.EnumUnderlyingType:type;
            var types=owner.AppContext.SystemTypes;
            if(ReferenceEquals(scalar,types.SystemSingleType))return new FloatLiteral(0f);
            if(ReferenceEquals(scalar,types.SystemDoubleType))return new DoubleLiteral(0d);
            TypeAnalysisContext[] integral=[types.SystemBooleanType,types.SystemByteType,types.SystemSByteType,
                types.SystemCharType,types.SystemInt16Type,types.SystemUInt16Type,
                types.SystemInt32Type,types.SystemUInt32Type,types.SystemInt64Type,types.SystemUInt64Type];
            return type.IsValueType && integral.Any(t=>ReferenceEquals(t,scalar))?new Immediate(0):null;
        }
        var arguments=new List<IOperand>();
        foreach(var parameter in ctor.Parameters)
        {
            if(Zero(parameter.ParameterType) is not {} zero)return null;
            arguments.Add(zero);
        }
        var fields=new HashSet<FieldAnalysisContext>();var ranges=new List<(long Start,long End)>();
        foreach(var assignment in template.Assignments)
        {
            var field=assignment.Field;var width=PlainScalarWidth(field,owner.AppContext.Binary.PointerSizeBytes);
            if(!OwnsField(owner,field) || !fields.Add(field) || field.Offset<16 || width<=0
                || assignment.NativeWidth!=width)return null;
            var start=(long)field.Offset;var end=start+width;
            if(ranges.Any(r=>start<r.End && r.Start<end))return null;
            ranges.Add((start,end));
            if(assignment.Constant is {} constant)
            {
                if(Zero(field.FieldType) is not {} zero || !SameValue(constant,zero))return null;
            }
            else if(assignment.Parameter<0 || assignment.Parameter>=arguments.Count)return null;
        }
        return arguments.ToArray();
    }

    private static int PlainScalarWidth(FieldAnalysisContext field,int pointerSize)
    {
        var raw=field.BackingData?.Field.RawFieldType;
        if(raw!=null && (raw.NumMods!=0 || raw.Byref!=0 || raw.Pinned!=0))return 0;
        var scalar=field.FieldType.IsEnumType?field.FieldType.EnumUnderlyingType:field.FieldType;
        var types=field.AppContext.SystemTypes;
        TypeAnalysisContext[] supported=[types.SystemBooleanType,types.SystemByteType,types.SystemSByteType,
            types.SystemCharType,types.SystemInt16Type,types.SystemUInt16Type,types.SystemInt32Type,types.SystemUInt32Type,
            types.SystemInt64Type,types.SystemUInt64Type,types.SystemSingleType,types.SystemDoubleType];
        return field.FieldType.IsValueType && supported.Any(type=>ReferenceEquals(type,scalar))
            ? FieldWidth(field,pointerSize):0;
    }

    private static bool ScalarStores(Template template,TypeAnalysisContext owner,
        List<(Instruction Instruction,FieldAnalysisContext Field)> stores)
    {
        if(!RootNoOp(template,owner) || !ScalarSetupClass(owner)
            || stores.Count!=template.Assignments.Count)return false;
        var ranges=new List<(long Start,long End)>();
        foreach(var assignment in template.Assignments)
        {
            var field=assignment.Field;var width=PlainScalarWidth(field,owner.AppContext.Binary.PointerSizeBytes);
            var actual=stores.SingleOrDefault(s=>ReferenceEquals(s.Field,field)).Instruction;
            if(width<=0 || field.Offset<16 || assignment.NativeWidth!=width || actual==null
                || actual.NativeWriteSize!=width
                || actual.Operands[0] is FieldReference reference && reference.Offset!=field.Offset)return false;
            var start=(long)field.Offset;var end=start+width;
            if(ranges.Any(r=>start<r.End && r.Start<end))return false;
            ranges.Add((start,end));
        }
        return true;
    }

    private static bool UsesLocal(IOperand? operand,LocalVariable local,int depth=0)
    {
        if(depth>8)return true;
        if(ReferenceEquals(operand,local))return true;
        return operand switch
        {
            AddressOf address=>UsesLocal(address.Target,local,depth+1),
            MemoryOperand memory=>UsesLocal(memory.Base,local,depth+1)||UsesLocal(memory.Index,local,depth+1),
            FieldReference field=>ReferenceEquals(field.Local,local)||UsesLocal(field.Parent,local,depth+1),
            _=>false,
        };
    }

    private static Block? LinearSetupBlock(MethodAnalysisContext method,Block allocationBlock,Instruction instruction)
    {
        var block=allocationBlock;var seen=new HashSet<Block>();
        while(seen.Add(block))
        {
            if(block.Instructions.Contains(instruction))return block;
            if(block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)return null;
            block=block.Successors[0];
        }
        return null;
    }

    private static int IntegralSetupWidth(TypeAnalysisContext? type,SystemTypesContext types)
    {
        if(type?.IsEnumType==true)type=type.EnumUnderlyingType;
        if(ReferenceEquals(type,types.SystemInt32Type)||ReferenceEquals(type,types.SystemUInt32Type))return 4;
        if(ReferenceEquals(type,types.SystemInt64Type)||ReferenceEquals(type,types.SystemUInt64Type))return 8;
        return 0;
    }

    private static bool SetupScalarValue(Instruction instruction,MethodAnalysisContext method,
        List<Instruction> instructions,int allocationIndex,Block allocationBlock,List<Instruction> pending,
        ref DominatorInfo? dominance,ISet<LocalVariable> aliases)
    {
        if(instruction.Destination is not LocalVariable destination || instruction.ImplicitDefinition!=null
            || LinearSetupBlock(method,allocationBlock,instruction)==null
            || destination.IsThis || destination.IsMethodInfo || destination.IsReturnBuffer
            || method.ParameterLocals.Contains(destination) || aliases.Contains(destination))return false;
        var types=method.AppContext.SystemTypes;
        IOperand[] inputs;
        if(instruction is {OpCode:OpCode.NumericConvert,
            Operands:[_,TypeAnalysisContext target,TypeAnalysisContext source,LocalVariable input]})
        {
            if(!TrivialConstructorRecovery.SameType(destination.Type,target)
                || !TrivialConstructorRecovery.SameType(input.Type,source)
                || !(ReferenceEquals(target,types.SystemSingleType)&&ReferenceEquals(source,types.SystemDoubleType)
                    || ReferenceEquals(target,types.SystemDoubleType)&&ReferenceEquals(source,types.SystemSingleType)))return false;
            inputs=[input];
        }
        else if(instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply
            && instruction.Operands.Count==3 && instruction.NativeArithmeticSize is 4 or 8
            && instruction.NativeMultiplyInputSize is 0
            && IntegralSetupWidth(destination.Type,types)==instruction.NativeArithmeticSize
            && IlGenerator.NativeIntegerArithmeticType(instruction,method)!=null)
        {
            inputs=instruction.Operands.Skip(1).ToArray();
            if(inputs.Any(value=>value is not Immediate
                && (value is not LocalVariable local || IntegralSetupWidth(local.Type,types)!=instruction.NativeArithmeticSize)))return false;
        }
        else return false;
        if(instructions.Count(i=>ReferenceEquals(i.Destination,destination))!=1
            || instructions.Take(allocationIndex+1).Any(i=>i.Sources.Any(o=>UsesLocal(o,destination)))
            || instructions.Any(i=>i.Operands.Any(o=>o is AddressOf or MemoryOperand or FieldReference
                && UsesLocal(o,destination))))return false;
        foreach(var value in inputs)
        {
            if(value is Immediate)continue;
            if(value is not LocalVariable local || ReferenceEquals(local,destination)
                || local.IsThis || local.IsMethodInfo || local.IsReturnBuffer || aliases.Contains(local))return false;
            if(!pending.Any(i=>ReferenceEquals(i.Destination,local))
                && !AvailableBeforeAllocation(local,method,instructions,allocationIndex,allocationBlock,ref dominance,aliases))return false;
        }
        return true;
    }

    public static bool Recover(MethodAnalysisContext method, Instruction allocation, IReadOnlyList<Template> templates)
        => RecoverCore(method,allocation,templates,method.AppContext.UnityVersion.Major==2018
            && method.AppContext.UnityVersion.Minor==4 && method.AppContext.Binary.PointerSizeBytes==8
            && method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet);

    internal static bool RecoverScalarSetup(MethodAnalysisContext method, Instruction allocation, IReadOnlyList<Template> templates)
        => RecoverCore(method,allocation,templates,true);

    private static bool RecoverCore(MethodAnalysisContext method, Instruction allocation, IReadOnlyList<Template> templates,
        bool scalarSetup)
    {
        if (allocation is not { OpCode: OpCode.Newobj, Operands: [LocalVariable obj, TypeAnalysisContext type] }
            || type.IsValueType || type.BaseType==null || type.HasAnyGenericParameters()) return false;
        var objectBase=type.BaseType.FullName=="System.Object";
        var proven=templates.Where(t=>ReferenceEquals(t.Constructor.DeclaringType,type)
            && (t.BaseConstructor!=null ? DirectBase(type,t.BaseConstructor)
                && (t.BaseArguments?.Count??0)==t.BaseConstructor.Parameters.Count : objectBase)).ToArray();
        if(proven.Length==0)return false;
        var instructions = method.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(allocation);
        if (index < 0) return false;
        var allocationBlock = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(allocation));
        var scan = allocationBlock.Instructions.Skip(allocationBlock.Instructions.IndexOf(allocation)+1).ToList();
        var visited = new HashSet<Block> {allocationBlock};
        var current = allocationBlock;
        // BFS instruction order is NOT execution order across branches. Only a
        // single-entry straight-line continuation belongs to this initialization.
        while (current.Successors.Count == 1 && current.Successors[0].Predecessors.Count == 1
            && visited.Add(current.Successors[0]))
        { current = current.Successors[0]; scan.AddRange(current.Instructions); }
        DominatorInfo? dominance = null;
        var aliases = new HashSet<LocalVariable> {obj};
        Instruction? baseCall = null;
        var conversions=new List<Instruction>();
        var stores = new List<(Instruction Instruction, FieldAnalysisContext Field)>();
        var matches = new List<(Template Template, IOperand[] Args)>();
        foreach (var instruction in scan)
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump) continue;
            if (scalarSetup && baseCall==null && stores.Count==0 && conversions.Count<8
                && proven.Any(t=>RootNoOp(t,type)) && ScalarSetupClass(type)
                && SetupScalarValue(instruction,method,instructions,index,allocationBlock,conversions,ref dominance,aliases))
            { conversions.Add(instruction);continue; }
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable alias, LocalVariable source] } && aliases.Contains(source))
            { aliases.Add(alias); continue; }
            if (instruction is { OpCode: OpCode.CallVoid, NativeVirtualDispatch:false,
                    Operands: [MethodAnalysisContext parent, LocalVariable receiver,..] }
                && instruction.Operands.Count==parent.Parameters.Count+2
                && DirectBase(type,parent)
                && proven.Any(t=>t.BaseConstructor!=null ? ReferenceEquals(t.BaseConstructor,parent) : objectBase)
                && aliases.Contains(receiver) && baseCall == null && stores.Count == 0)
            {
                if(instruction.Operands.Skip(2).Any(value=>!objectBase && value is FieldReference
                    || !AvailableBeforeAllocation(value,method,instructions,index,allocationBlock,ref dominance,aliases)))break;
                baseCall = instruction; continue;
            }
            if (baseCall == null || instruction is not { OpCode: OpCode.Move, Operands: [_, var value] }
                || StoreField(instruction,type,aliases,method.AppContext.Binary.PointerSizeBytes) is not {} field
                || stores.Any(s => s.Field == field)
                // A nontrivial parent may publish this or invoke callbacks.
                // Never move a field read across that call: only already
                // materialized locals/literals can become child arguments.
                || !objectBase && value is FieldReference
                || !AvailableBeforeAllocation(value, method, instructions, index, allocationBlock, ref dominance, aliases)
                    && !conversions.Any(c=>ReferenceEquals(c.Destination,value))) break;
            stores.Add((instruction,field));
            matches.Clear();
            foreach (var template in proven.Where(t => t.Assignments.Count == stores.Count
                && (t.BaseConstructor==null || ReferenceEquals(t.BaseConstructor,baseCall.Operands[0]))))
            {
                var commuting=scalarSetup && ScalarStores(template,type,stores);
                if(conversions.Count>0 && !commuting)continue;
                if(!objectBase && !template.Assignments.Select(a=>a.Field)
                    .SequenceEqual(stores.Select(s=>s.Field)) && !commuting)continue;
                var args = new IOperand[template.Constructor.Parameters.Count];
                var valid = true;
                var bindings=template.BaseArguments??[];
                for(var n=0;n<bindings.Count;n++)
                {
                    var binding=bindings[n];var actual=baseCall.Operands[n+2];
                    if(binding.Constant is {} constant)
                    {if(binding.Parameter!=-1 || !SameValue(constant,actual)){valid=false;break;}continue;}
                    if(binding.Parameter<0 || binding.Parameter>=args.Length
                        || args[binding.Parameter] is {} previous && !SameValue(previous,actual))
                    {valid=false;break;}
                    args[binding.Parameter]=actual;
                }
                if(!valid)continue;
                foreach (var assignment in template.Assignments)
                {
                    var store = stores.SingleOrDefault(s => s.Field == assignment.Field).Instruction;
                    if (store == null) { valid = false; break; }
                    var argument = store.Operands[1];
                    if (assignment.Constant is { } constant)
                    {
                        if (assignment.Parameter != -1 || !SameValue(constant, argument)) { valid = false; break; }
                        continue;
                    }
                    if (assignment.Parameter < 0 || assignment.Parameter >= args.Length) { valid = false; break; }
                    if (args[assignment.Parameter] is { } previous && !SameValue(previous, argument)) { valid = false; break; }
                    args[assignment.Parameter] = argument;
                }
                if (valid && args.All(a => a != null)) matches.Add((template,args));
            }
            if (matches.Count > 0) break;
        }
        if (baseCall == null || matches.Count != 1) return false;
        var match = matches[0];
        // Commit the whole match at once. Failed/ambiguous candidates never
        // move definitions or make future locals available to IL newobj.
        var insertion=allocationBlock.Instructions.IndexOf(allocation);
        foreach(var conversion in conversions)
        {
            var originalBlock=method.ControlFlowGraph!.Blocks.Single(b=>b.Instructions.Contains(conversion));
            originalBlock.Instructions.Remove(conversion);
            allocationBlock.Instructions.Insert(insertion++,conversion);
        }
        baseCall.SetOperands(new List<IOperand> {match.Template.Constructor,obj}.Concat(match.Args).ToList());
        foreach (var (store,_) in stores) { store.OpCode = OpCode.Nop; store.SetOperands(); }
        return true;
    }

    // Allocation types can become known after the last field-resolution sweep.
    // Bind only a complete scalar/reference store at an exact declared offset;
    // do not rewrite the graph or infer an owner from a propagated base type.
    private static FieldAnalysisContext? StoreField(Instruction instruction,TypeAnalysisContext owner,
        ISet<LocalVariable> aliases,int pointerSize)
    {
        if(instruction.Operands[0] is FieldReference field)
            return field.Parent==null && aliases.Contains(field.Local) && !field.Field.IsStatic
                && OwnsField(owner,field.Field)
                && (ReferenceEquals(field.Field.DeclaringType,owner)
                    || field.Offset==field.Field.Offset && instruction.NativeWriteSize>0
                        && instruction.NativeWriteSize==FieldWidth(field.Field,pointerSize)) ? field.Field : null;
        if(instruction.Operands[0] is not MemoryOperand {Base:LocalVariable receiver,Index:null,Scale:0} memory
            || !aliases.Contains(receiver) || memory.Addend<2L*pointerSize || instruction.NativeWriteSize<=0)return null;
        if(Hierarchy(owner) is not {} hierarchy)return null;
        var fields=hierarchy.SelectMany(t=>t.Fields).Where(f=>OwnsField(owner,f)
            && f.Offset==memory.Addend).ToArray();
        if(fields.Length!=1)return null;
        var width=FieldWidth(fields[0],pointerSize);
        return width==instruction.NativeWriteSize?fields[0]:null;
    }

    internal static bool AvailableBeforeAllocation(IOperand value, MethodAnalysisContext method,
        List<Instruction> instructions, int allocationIndex, Block allocationBlock,
        ref DominatorInfo? dominance, ISet<LocalVariable> aliases)
    {
        if (value is Immediate or FloatLiteral or DoubleLiteral or StringLiteral) return true;
        if (value is FieldReference { Field.IsStatic: false } field)
        {
            // The canonical managed instance receiver is non-null on entry. Do
            // not extend this to arbitrary reference parameters or this aliases:
            // moving their field reads would move a possible null exception.
            if (field.Local.IsThis && method.ParameterLocals.Any(p=>ReferenceEquals(p,field.Local)))
                return !aliases.Contains(field.Local);
            return field.Local.Type?.IsValueType == true && AvailableBeforeAllocation(field.Local,
                method,instructions,allocationIndex,allocationBlock,ref dominance,aliases);
        }
        if (value is not LocalVariable local || aliases.Contains(local)) return false;
        var definitions = instructions.Select((i,n)=>(i,n)).Where(x => ReferenceEquals(x.i.Destination,local)).ToList();
        if (definitions.Count == 0) return method.ParameterLocals.Contains(local);
        // A loop local can be assigned again AFTER initialization. We load its
        // current value at allocation, not a frozen SSA version. The scanned
        // initialization contains no writes to argument locals, so subsequent
        // loop increments cannot change any value moved to the constructor call.
        foreach (var definition in definitions.Where(d => d.n < allocationIndex))
        {
            var definitionBlock = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(definition.i));
            if (definitionBlock == allocationBlock) return true;
            dominance ??= new DominatorInfo(method.ControlFlowGraph);
            if (dominance.Dominates(definitionBlock, allocationBlock)) return true;
        }
        // Phi elimination leaves one local assigned on each incoming branch.
        // No individual definition dominates a join. Prove an assignment on
        // EVERY predecessor path; an unanchored cycle or missing path rejects.
        var memo = new Dictionary<Block,bool>();
        var visiting = new HashSet<Block>();
        bool AssignedOnEntry(Block block)
        {
            if (memo.TryGetValue(block,out var known)) return known;
            if (!visiting.Add(block)) return false;
            var available = block.Predecessors.Count > 0 && block.Predecessors.All(before =>
                before.Instructions.Any(i=>ReferenceEquals(i.Destination,local)) || AssignedOnEntry(before));
            visiting.Remove(block);
            memo[block]=available;
            return available;
        }
        return AssignedOnEntry(allocationBlock);
    }

    private static bool ExactConstant(TypeAnalysisContext type, IOperand value)
    {
        if (value is FloatLiteral) return type.FullName == "System.Single";
        if (value is DoubleLiteral) return type.FullName == "System.Double";
        if (value is StringLiteral) return type.FullName == "System.String";
        if (value is not Immediate immediate) return false;
        if (!type.IsValueType) return immediate.Value == 0 && type.Type is
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_CLASS or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_STRING or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY;
        var scalar = type.IsEnumType ? type.EnumUnderlyingType : type;
        return scalar?.FullName switch
        {
            "System.Boolean" => immediate.Value is 0 or 1,
            "System.SByte" => immediate.Value is >= sbyte.MinValue and <= sbyte.MaxValue,
            "System.Byte" => immediate.Value is >= byte.MinValue and <= byte.MaxValue,
            "System.Int16" => immediate.Value is >= short.MinValue and <= short.MaxValue,
            "System.UInt16" or "System.Char" => immediate.Value is >= ushort.MinValue and <= ushort.MaxValue,
            "System.Int32" => immediate.Value is >= int.MinValue and <= int.MaxValue,
            "System.UInt32" => immediate.Value is >= uint.MinValue and <= uint.MaxValue,
            "System.Int64" or "System.UInt64" => true,
            _ => false
        };
    }

    private static bool SameValue(IOperand a, IOperand b) => ReferenceEquals(a,b) || (a,b) switch
    {
        (Immediate x,Immediate y) => x.Value == y.Value,
        (FloatLiteral x,FloatLiteral y) => System.BitConverter.SingleToInt32Bits(x.Value) == System.BitConverter.SingleToInt32Bits(y.Value),
        (DoubleLiteral x,DoubleLiteral y) => System.BitConverter.DoubleToInt64Bits(x.Value) == System.BitConverter.DoubleToInt64Bits(y.Value),
        (StringLiteral x,StringLiteral y) => x.Value == y.Value,
        (FieldReference x,FieldReference y) => x.Field == y.Field && ReferenceEquals(x.Local,y.Local),
        _ => false
    };
}
