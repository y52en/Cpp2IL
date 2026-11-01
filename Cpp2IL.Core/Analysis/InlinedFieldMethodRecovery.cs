using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Immutable native-derived templates, prepared before parallel IL emission.
// Restore small nonvirtual field-update methods, never widen field visibility.
public static class InlinedFieldMethodRecovery
{
    public const string CacheKey = "NativeInlineFieldMethodTemplates";
    public sealed record Store(FieldAnalysisContext Field, int Parameter, IOperand? Constant = null)
    { public int NativeWidth {get;init;} }
    public sealed record Template(MethodAnalysisContext Method, Store[] Stores,
        MethodAnalysisContext? Tail, int[] TailParameters, bool TailVirtualDispatch = false);

    static bool InHierarchy(TypeAnalysisContext owner, TypeAnalysisContext? target)
    {
        var visited=new HashSet<TypeAnalysisContext>();
        for(var type=owner;type!=null && visited.Add(type);type=type.BaseType)
            if(TrivialConstructorRecovery.SameType(type,target))return true;
        return false;
    }

    static bool ProvenConstant(TypeAnalysisContext type,IOperand value)
    {
        if(value is FloatLiteral)return type.FullName=="System.Single";
        if(value is DoubleLiteral)return type.FullName=="System.Double";
        if(value is not Immediate immediate)return false;
        if(!type.IsValueType)return immediate.Value==0;
        if(type.IsEnumType)
        {
            if(type.EnumUnderlyingType is not {} underlying)return false;
            type=underlying;
        }
        return type.FullName switch {
            "System.Boolean" => immediate.Value is 0 or 1,
            "System.SByte" => immediate.Value is >=sbyte.MinValue and <=sbyte.MaxValue,
            "System.Byte" => immediate.Value is >=byte.MinValue and <=byte.MaxValue,
            "System.Int16" => immediate.Value is >=short.MinValue and <=short.MaxValue,
            "System.UInt16" => immediate.Value is >=ushort.MinValue and <=ushort.MaxValue,
            "System.Int32" => immediate.Value is >=int.MinValue and <=int.MaxValue,
            "System.UInt32" => immediate.Value is >=0 and <=uint.MaxValue,
            "System.Int64" or "System.UInt64" => true,
            _ => false };
    }

    static int? VoidReceiverIndex(Instruction call, Cpp2IL.Core.Graphs.ISILControlFlowGraph cfg)
    {
        if(call.Operands.Count==0 || call.Operands[0] is not MethodAnalysisContext {IsVoid:true})return null;
        if(call.OpCode==OpCode.CallVoid)return 1;
        // A late-resolved void target may retain the lifter's result slot.
        // Never discard an observed native result use or reinterpret it as this.
        if(call.OpCode!=OpCode.Call || call.Operands.Count<3 || call.Operands[1] is not LocalVariable result
            || call.Operands.Skip(2).Any(o=>References(o,result))
            || cfg.Instructions.Any(i=>i.Operands.Where((o,n)=>n!=1 || !ReferenceEquals(i,call))
                .Any(o=>!ReferenceEquals(o,i.Destination) && References(o,result))))return null;
        return 2;
    }

    static bool References(IOperand? operand,LocalVariable local) => operand switch {
        LocalVariable value => ReferenceEquals(value,local),
        MemoryOperand memory => References(memory.Base,local) || References(memory.Index,local),
        FieldReference field => References(field.Local,local) || References(field.Parent,local),
        AddressOf address => References(address.Target,local),
        ArrayAccess array => References(array.Array,local) || References(array.Index,local),
        ArrayLength length => References(length.Array,local),
        _ => false };

    public static Template? Extract(MethodAnalysisContext method)
    {
        if (method.IsStatic || method.IsVirtual || !method.IsVoid || method.Name.StartsWith(".")
            || method.GenericParameters.Count != 0 || method.DeclaringType is not { IsValueType: false } owner
            || (method.Attributes & MethodAttributes.MemberAccessMask) != MethodAttributes.Public
            || method.Parameters.Count is > 4 || method.ControlFlowGraph == null) return null;
        var cfg = method.ControlFlowGraph;
        var visited = new HashSet<Cpp2IL.Core.Graphs.Block>();
        var ordered = new List<Instruction>();
        var block = cfg.EntryBlock;
        while (block != cfg.ExitBlock)
        {
            if (!visited.Add(block) || block.Successors.Count != 1
                || block != cfg.EntryBlock && block.Predecessors.Count != 1) return null;
            ordered.AddRange(block.Instructions);
            block = block.Successors[0];
        }
        if (cfg.Blocks.Any(b => b.Instructions.Count > 0 && !visited.Contains(b))) return null;
        var parameters = method.ParameterLocals.Where(p => !p.IsThis && !p.IsMethodInfo).ToList();
        if (parameters.Count != method.Parameters.Count) return null;
        var instructions = ordered.Where(i => i.OpCode is not (OpCode.Nop or OpCode.Jump)).ToArray();
        if (instructions.Length < 2 || instructions.Last() is not { OpCode: OpCode.Return, Operands.Count: 0 }) return null;
        var stores = new List<Store>();
        MethodAnalysisContext? tail = null;
        var tailVirtual=false;
        var tailParameters = new List<int>();
        foreach (var instruction in instructions.Take(instructions.Length - 1))
        {
            if (tail != null) return null;
            if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference field, var argument] }
                && field.Parent == null && field.Local.IsThis && field.Field.DeclaringType == owner
                && !field.Field.IsStatic && field.Field.Offset >= 0 && field.Offset == field.Field.Offset
                && !stores.Any(s => s.Field == field.Field))
            {
                if(argument is FloatLiteral or DoubleLiteral
                    && instruction.NativeWriteSize!=(argument is FloatLiteral?4:8))return null;
                if(argument is Immediate or FloatLiteral or DoubleLiteral && ProvenConstant(field.Field.FieldType,argument))
                    stores.Add(new(field.Field,-1,argument){NativeWidth=instruction.NativeWriteSize});
                else if(argument is LocalVariable local)
                {
                    var index=parameters.IndexOf(local);
                    if(index<0 || !TrivialConstructorRecovery.SameType(local.Type,field.Field.FieldType))return null;
                    stores.Add(new(field.Field,index){NativeWidth=instruction.NativeWriteSize});
                }
                else return null;
            }
            else if (stores.Count > 0 && VoidReceiverIndex(instruction,cfg) is {} receiverIndex
                && instruction.Operands.Count > receiverIndex && instruction.Operands[0] is MethodAnalysisContext target
                && !target.IsStatic && target.IsVoid && InHierarchy(owner,target.DeclaringType)
                && (!instruction.NativeVirtualDispatch || target.IsVirtual)
                && target != method && instruction.Operands[receiverIndex] is LocalVariable { IsThis: true }
                && instruction.Operands.Count == target.Parameters.Count + receiverIndex + 1)
            {
                foreach (var value in instruction.Operands.Skip(receiverIndex+1))
                {
                    if (value is not LocalVariable local) return null;
                    var index = parameters.IndexOf(local);
                    if (index < 0) return null;
                    tailParameters.Add(index);
                }
                tail = target;
                tailVirtual=instruction.NativeVirtualDispatch;
            }
            else return null;
        }
        if (stores.Count == 0 || Enumerable.Range(0, parameters.Count).Any(p => stores.All(s => s.Parameter != p))) return null;
        return new(method, stores.ToArray(), tail, tailParameters.ToArray(),tailVirtual);
    }

    public static int Prepare(ApplicationAnalysisContext app, Func<MethodAnalysisContext, bool> skip)
    {
        var count = 0;
        foreach (var type in app.Assemblies.SelectMany(a => a.Types))
        {
            var templates = new List<Template>();
            if (type.IsValueType || type.GenericParameters.Count != 0) continue;
            foreach (var method in type.Methods.Where(m => !m.IsStatic && !m.IsVirtual && m.IsVoid
                && !m.Name.StartsWith(".") && m.Parameters.Count <= 4 && m.UnderlyingPointer != 0))
            {
                if (skip(method)) continue;
                try
                {
                    method.EnsureRawBytes();
                    if (method.RawBytes.Length is 0 or > 128) continue;
                    method.Analyze();
                    if (Extract(method) is { } template) templates.Add(template);
                }
                catch { /* Missing native proof never authorizes a substitution. */ }
                finally { method.ReleaseAnalysisData(); }
            }
            type.PutExtraData(CacheKey, templates.ToArray()); count += templates.Count;
        }
        return count;
    }

    public static int Run(MethodAnalysisContext caller)
        => Recover(caller,caller.AppContext.UnityVersion.Major==2018 && caller.AppContext.UnityVersion.Minor==4
            && caller.AppContext.Binary.PointerSizeBytes==8
            && caller.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet);

    private static int ScalarWidth(FieldAnalysisContext field)
    {
        var raw=field.BackingData?.Field.RawFieldType;
        if(raw!=null && (raw.NumMods!=0 || raw.Byref!=0 || raw.Pinned!=0))return 0;
        if(field.IsStatic || (field.Attributes&FieldAttributes.InitOnly)!=0)return 0;
        var type=field.FieldType.IsEnumType?field.FieldType.EnumUnderlyingType:field.FieldType;
        return type?.FullName switch {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32" or "System.Single"=>4,
            "System.Int64" or "System.UInt64" or "System.Double"=>8,_=>0};
    }

    private static bool IndependentScalarStores(Template template)
    {
        var owner=template.Method.DeclaringType!;var seen=new HashSet<TypeAnalysisContext>();
        for(var type=owner;type!=null;type=type.BaseType)
        {
            if(seen.Count>=32 || !seen.Add(type) || type.IsValueType || type.HasAnyGenericParameters()
                || (type.Attributes&TypeAttributes.LayoutMask)==TypeAttributes.ExplicitLayout
                || type.Methods.Any(m=>m.Name==".cctor" || m.Name=="Finalize"
                    && !ReferenceEquals(type,owner.AppContext.SystemTypes.SystemObjectType)))return false;
        }
        var fields=new HashSet<FieldAnalysisContext>();var ranges=new List<(long Start,long End)>();
        foreach(var store in template.Stores)
        {
            var field=store.Field;var width=ScalarWidth(field);
            if(width==0 || store.NativeWidth!=width || field.Offset<16 || !fields.Add(field)
                || !seen.Contains(field.DeclaringType))return false;
            var start=(long)field.Offset;var end=start+width;
            if(ranges.Any(r=>start<r.End && r.Start<end))return false;
            ranges.Add((start,end));
        }
        return fields.Count>0;
    }

    internal static int Recover(MethodAnalysisContext caller,bool allowScalarReordering)
    {
        // Constructor bodies have their own base/allocation reconstruction.
        // Their own fields are already accessible; leave that evidence intact.
        if (caller.ControlFlowGraph == null || caller.Name.StartsWith(".")) return 0;
        var count = 0;
        foreach (var block in caller.ControlFlowGraph.Blocks)
        {
            var instructions = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
            for (var index = 0; index < instructions.Length; index++)
            {
                if (instructions[index] is not { OpCode: OpCode.Move, Operands: [FieldReference field, _] }
                    || field.Local.Type != field.Field.DeclaringType
                    || field.Field.DeclaringType.GetExtraData<Template[]>(CacheKey) is not { } templates) continue;
                var matches = new List<(Template Template, IOperand[] Arguments, int Length)>();
                foreach (var template in templates.Where(t => t.Method != caller))
                {
                    // LLVM may commute independent scalar stores while
                    // inlining. Reference writes, unknown widths, overlaps,
                    // custom modifiers and class/finalizer effects never use
                    // this path. Argument expressions remain precomputed.
                    var reorder=allowScalarReordering && IndependentScalarStores(template);
                    var length = template.Stores.Length + (template.Tail == null ? 0 : 1);
                    if (index + length > instructions.Length) continue;
                    var arguments = new IOperand[template.Method.Parameters.Count];
                    var valid = true;
                    for (var n = 0; n < template.Stores.Length; n++)
                    {
                        if (instructions[index + n] is not { OpCode: OpCode.Move, Operands: [FieldReference actual, var value] }
                            || actual.Local != field.Local || actual.Parent != null
                            || value is not (LocalVariable or Immediate or FloatLiteral or DoubleLiteral)
                                && !(reorder && ScalarFieldArgument(template, value, instructions[index+n]))) { valid = false; break; }
                        var store=reorder?template.Stores.SingleOrDefault(s=>ReferenceEquals(s.Field,actual.Field)):template.Stores[n];
                        if(store==null || actual.Offset!=store.Field.Offset || actual.Field!=store.Field
                            || reorder && instructions[index+n].NativeWriteSize!=store.NativeWidth)
                        {valid=false;break;}
                        if(value is FloatLiteral or DoubleLiteral
                            && (!ProvenConstant(actual.Field.FieldType,value) || store.NativeWidth!=ScalarWidth(actual.Field)
                                || instructions[index+n].NativeWriteSize!=store.NativeWidth))
                        {valid=false;break;}
                        if(reorder && instructions.Skip(index).Take(n).Any(i=>i.Operands[0] is FieldReference previousField
                            && ReferenceEquals(previousField.Field,actual.Field))) {valid=false;break;}
                        if(store.Constant is {} constant)
                        {
                            if(!Same(constant,value)){valid=false;break;}
                            continue;
                        }
                        if (arguments[store.Parameter] is { } previous && !Same(previous, value)) { valid = false; break; }
                        arguments[store.Parameter] = value;
                    }
                    if (!valid || arguments.Any(a => a == null)) continue;
                    if (template.Tail != null)
                    {
                        var call = instructions[index + length - 1];
                        if (VoidReceiverIndex(call,caller.ControlFlowGraph) is not {} receiverIndex
                            || call.NativeVirtualDispatch!=template.TailVirtualDispatch || call.Operands.Count != template.TailParameters.Length + receiverIndex + 1
                            || call.Operands[0] != template.Tail || call.Operands[receiverIndex] != field.Local
                            || template.TailParameters.Where((p, n) => !Same(arguments[p], call.Operands[n + receiverIndex + 1])).Any()) continue;
                    }
                    matches.Add((template, arguments, length));
                }
                if (matches.Count != 1 && allowScalarReordering && ConstantReset(matches) is {} reset)
                {
                    matches.Clear(); matches.Add(reset);
                }
                if (matches.Count != 1) continue;
                var match = matches[0];
                instructions[index].OpCode = OpCode.CallVoid;
                instructions[index].SetOperands(new List<IOperand> { match.Template.Method, field.Local }.Concat(match.Arguments).ToList());
                for (var n = 1; n < match.Length; n++) { instructions[index + n].OpCode = OpCode.Nop; instructions[index + n].SetOperands(); }
                index += match.Length - 1; count++;
            }
        }
        return count;
    }

    // A single scalar store can evaluate one same-receiver field argument at
    // the exact original read/store point. Multiple stores may read values
    // changed by earlier stores; never turn those reads into eager arguments.
    private static bool ScalarFieldArgument(Template template, IOperand value, Instruction instruction)
    {
        if (template.Stores.Length != 1 || template.Tail != null || template.Method.Parameters.Count != 1
            || value is not FieldReference { Parent: null } source
            || instruction.Operands[0] is not FieldReference destination
            || !ReferenceEquals(source.Local,destination.Local)
            || !ReferenceEquals(source.Field.DeclaringType,template.Method.DeclaringType)
            || !ReferenceEquals(source.Local.Type,source.Field.DeclaringType)
            || source.Offset != source.Field.Offset || source.Offset < 16)return false;
        var width=ScalarWidth(source.Field);
        return width>0 && instruction.NativeWriteSize==width
            && (instruction.NativeReadSize==0 || instruction.NativeReadSize==width)
            && template.Stores[0].NativeWidth==width
            && TrivialConstructorRecovery.SameType(source.Field.FieldType,template.Method.Parameters[0].ParameterType)
            && TrivialConstructorRecovery.SameType(source.Field.FieldType,destination.Field.FieldType);
    }

    // A parameterized setter and one constant reset may encode the same
    // complete native effect for these exact literal arguments. Prefer the
    // uniquely specialized reset; never choose by name or guess between two
    // resets. Unknown widths, references, lifecycle effects and tails reject.
    private static (Template Template, IOperand[] Arguments, int Length)? ConstantReset(
        List<(Template Template, IOperand[] Arguments, int Length)> matches)
    {
        if(matches.Count<2)return null;
        var candidates=matches.Where(m=>m.Template.Method.Parameters.Count==0
            && m.Template.Tail==null && m.Template.Stores.All(s=>s.Constant!=null)
            && IndependentScalarStores(m.Template)).ToArray();
        if(candidates.Length!=1)return null;
        var reset=candidates[0];
        foreach(var other in matches)
        {
            if(other.Length!=reset.Length || other.Template.Tail!=null
                || !IndependentScalarStores(other.Template))return null;
            foreach(var store in other.Template.Stores)
            {
                var expected=reset.Template.Stores.SingleOrDefault(s=>ReferenceEquals(s.Field,store.Field));
                if(expected==null || expected.NativeWidth!=store.NativeWidth)return null;
                var value=store.Constant ?? (store.Parameter>=0 && store.Parameter<other.Arguments.Length
                    ?other.Arguments[store.Parameter]:null);
                if(value==null || !Same(expected.Constant!,value))return null;
            }
        }
        return reset;
    }

    static bool Same(IOperand a, IOperand b) => ReferenceEquals(a, b) || (a,b)switch {
        (Immediate x,Immediate y)=>x.Value==y.Value,
        (FloatLiteral x,FloatLiteral y)=>BitConverter.SingleToInt32Bits(x.Value)==BitConverter.SingleToInt32Bits(y.Value),
        (DoubleLiteral x,DoubleLiteral y)=>BitConverter.DoubleToInt64Bits(x.Value)==BitConverter.DoubleToInt64Bits(y.Value),
        _=>false};
}
