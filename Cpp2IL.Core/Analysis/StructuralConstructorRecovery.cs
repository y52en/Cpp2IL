using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Complete, immutable native constructor templates. Unlike a name/signature
// match, this proves every store and the exact ordered floating expression.
// Reference traversals, integer arithmetic, callbacks and partial aggregates
// deliberately remain unsupported.
public static class StructuralConstructorRecovery
{
    public const string CacheKey = "NativeStructuralConstructorTemplates";
    public abstract record Expression;
    public sealed record Input(int Parameter, FieldAnalysisContext[] Path) : Expression;
    public sealed record Binary(OpCode Operation, Expression Left, Expression Right) : Expression;
    public sealed record Store(FieldAnalysisContext[] Path, Expression Value);
    public sealed record Template(MethodAnalysisContext Constructor, Store[] Stores, Input[] Inputs);

    static FieldAnalysisContext[] Path(FieldReference field) => field.Parent == null
        ? [field.Field] : [..Path(field.Parent), field.Field];
    static bool SamePath(FieldAnalysisContext[] a, FieldAnalysisContext[] b) => a.SequenceEqual(b);
    static bool SameValue(IOperand a, IOperand b) => ReferenceEquals(a,b) || (a,b) switch
    {
        (FloatLiteral x,FloatLiteral y) => System.BitConverter.SingleToInt32Bits(x.Value)==System.BitConverter.SingleToInt32Bits(y.Value),
        (FieldReference x,FieldReference y) => ReferenceEquals(x.Local,y.Local) && SamePath(Path(x),Path(y)),
        _ => false
    };
    static TypeAnalysisContext? ValueType(IOperand value) => value switch
    { LocalVariable local => local.Type, FieldReference field => field.Field.FieldType, _ => null };
    static bool Single(IOperand value) => value is FloatLiteral || ValueType(value)?.FullName=="System.Single";
    static bool FloatOperation(Instruction instruction) => instruction.OpCode is
        OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
        && instruction.NativeFloatingPointSize==4
        && instruction.Operands is [LocalVariable {Type.FullName:"System.Single"},var a,var b]
        && Single(a) && Single(b);

    static bool ValidPath(TypeAnalysisContext root, FieldAnalysisContext[] path)
    {
        if(path.Length is 0 or >8)return false;
        for(var i=0;i<path.Length;i++)
        {
            var field=path[i];
            if(field.IsStatic || !TrivialConstructorRecovery.SameType(field.DeclaringType,root))return false;
            root=field.FieldType;
            if(i<path.Length-1 && (!root.IsValueType || root.HasAnyGenericParameters()))return false;
        }
        return root.FullName=="System.Single";
    }

    // Full byte coverage is required before synthesizing an aggregate argument.
    // Padding, explicit overlaps, generic layout uncertainty and references fail.
    static FieldAnalysisContext[][]? Leaves(TypeAnalysisContext type, HashSet<TypeAnalysisContext>? seen=null)
    {
        if(type.FullName=="System.Single")return [[]];
        seen=seen==null?[]:new(seen);
        if(!type.IsValueType || type.HasAnyGenericParameters() || !seen.Add(type) || seen.Count>8)return null;
        var size=TypeSizes.UnboxedSize(type,type.AppContext.Binary.PointerSizeBytes);
        if(size is <=0 or >128)return null;
        var fields=type.Fields.Where(f=>!f.IsStatic).OrderBy(f=>f.Offset).ToArray();
        long end=0;var result=new List<FieldAnalysisContext[]>();
        foreach(var field in fields)
        {
            if(field.Offset!=end || Leaves(field.FieldType,seen) is not {} nested)return null;
            end+=field.FieldType.FullName=="System.Single"?4:TypeSizes.UnboxedSize(field.FieldType,type.AppContext.Binary.PointerSizeBytes);
            result.AddRange(nested.Select(p=>new[]{field}.Concat(p).ToArray()));
        }
        return end==size && result.Count>0?result.ToArray():null;
    }

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid
            || constructor.DeclaringType?.BaseType?.FullName!="System.Object"
            || constructor.DeclaringType.HasAnyGenericParameters() || constructor.ControlFlowGraph is not {} cfg)return null;
        var parameters=constructor.ParameterLocals.Where(l=>!l.IsThis && !l.IsMethodInfo).ToArray();
        if(parameters.Length!=constructor.Parameters.Count || parameters.Length==0)return null;
        var inputs=new List<Input>();
        for(var n=0;n<parameters.Length;n++)
        {
            if(parameters[n].Type is not {} type || Leaves(type) is not {} leaves)return null;
            inputs.AddRange(leaves.Select(p=>new Input(n,p)));
        }
        var ordered=new List<Instruction>();var visited=new HashSet<Block>();var block=cfg.EntryBlock;
        while(visited.Add(block))
        {
            ordered.AddRange(block.Instructions);
            if(ReferenceEquals(block,cfg.ExitBlock))break;
            if(block.Successors.Count!=1)return null;
            block=block.Successors[0];
        }
        if(!visited.Contains(cfg.ExitBlock) || cfg.Blocks.Any(b=>!visited.Contains(b)))return null;
        var expressions=new Dictionary<LocalVariable,Expression>();
        var self=new HashSet<LocalVariable>(constructor.ParameterLocals.Where(l=>l.IsThis));
        Expression? Read(IOperand value)
        {
            if(value is LocalVariable local)
            {
                var n=System.Array.IndexOf(parameters,local);
                if(n>=0 && local.Type?.FullName=="System.Single")return new Input(n,[]);
                return expressions.GetValueOrDefault(local);
            }
            if(value is FieldReference field)
            {
                var n=System.Array.IndexOf(parameters,field.Local);var path=Path(field);
                if(n>=0 && ValidPath(parameters[n].Type!,path))return new Input(n,path);
            }
            return null;
        }
        var stores=new List<Store>();var baseCalls=0;var returned=false;
        foreach(var instruction in ordered)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(returned)return null;
            if(instruction is {OpCode:OpCode.Return,Operands.Count:0}){returned=true;continue;}
            if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                Operands:[MethodAnalysisContext {Name:".ctor",DeclaringType.FullName:"System.Object",Parameters.Count:0},LocalVariable receiver]}
                && self.Contains(receiver) && ++baseCalls==1)continue;
            if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable target,LocalVariable source]} && self.Contains(source))
            {if(self.Contains(target) || expressions.ContainsKey(target))return null;self.Add(target);continue;}
            if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable destination,var value]} && Read(value) is {} expression)
            {if(parameters.Contains(destination) || !expressions.TryAdd(destination,expression) || self.Contains(destination))return null;continue;}
            if(FloatOperation(instruction) && Read(instruction.Operands[1]) is {} left && Read(instruction.Operands[2]) is {} right)
            {if(parameters.Contains((LocalVariable)instruction.Operands[0]) || !expressions.TryAdd((LocalVariable)instruction.Operands[0],new Binary(instruction.OpCode,left,right)))return null;continue;}
            if(instruction is {OpCode:OpCode.Move,Operands:[FieldReference field,var stored]}
                && self.Contains(field.Local) && ValidPath(constructor.DeclaringType,Path(field)) && Read(stored) is {} storedExpression)
            {
                var path=Path(field);
                if(baseCalls!=1 || stores.Any(s=>SamePath(s.Path,path)))return null;
                stores.Add(new(path,storedExpression));continue;
            }
            return null;
        }
        return returned && baseCalls==1 && stores.Count>0?new(constructor,stores.ToArray(),inputs.ToArray()):null;
    }

    public static void Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph==null)return;
        foreach(var allocation in method.ControlFlowGraph.Instructions.ToArray())
            if(allocation is {OpCode:OpCode.Newobj,Operands:[LocalVariable,TypeAnalysisContext type]}
                && type.GetExtraData<Template[]>(CacheKey) is {Length:>0} templates)Recover(method,allocation,templates);
    }

    public static bool Recover(MethodAnalysisContext method,Instruction allocation,IReadOnlyList<Template> templates)
    {
        if(method.ControlFlowGraph is not {} cfg || allocation.Operands is not [LocalVariable obj,TypeAnalysisContext type])return false;
        var all=cfg.Instructions;var index=all.IndexOf(allocation);if(index<0)return false;
        var home=cfg.Blocks.Single(b=>b.Instructions.Contains(allocation));
        var scan=new List<Instruction>();var block=home;var seen=new HashSet<Block>();var start=block.Instructions.IndexOf(allocation)+1;
        while(seen.Add(block))
        {
            scan.AddRange(block.Instructions.Skip(start));
            if(block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)break;
            block=block.Successors[0];start=0;
        }
        var definitions=all.Where(i=>i.Destination is LocalVariable).GroupBy(i=>(LocalVariable)i.Destination!)
            .Where(g=>g.Count()==1).ToDictionary(g=>g.Key,g=>g.Single());
        var aliases=new HashSet<LocalVariable>{obj};Instruction? baseCall=null;
        var stores=new List<Instruction>();DominatorInfo? dominance=null;
        foreach(var instruction in scan)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]} && aliases.Contains(source))
            {if(aliases.Contains(alias))break;aliases.Add(alias);continue;}
            if(baseCall==null && instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                Operands:[MethodAnalysisContext {Name:".ctor",DeclaringType.FullName:"System.Object",Parameters.Count:0},LocalVariable receiver]}
                && aliases.Contains(receiver)){baseCall=instruction;continue;}
            if(baseCall==null || instruction is not {OpCode:OpCode.Move,Operands:[FieldReference field,var value]}
                || !aliases.Contains(field.Local) || !ValidPath(type,Path(field))
                || stores.Any(s=>SamePath(Path((FieldReference)s.Operands[0]),Path(field))))break;
            stores.Add(instruction);
            var matches=new List<(Template Template,Dictionary<Input,IOperand> Values)>();
            foreach(var template in templates.Where(t=>ReferenceEquals(t.Constructor.DeclaringType,type) && t.Stores.Length==stores.Count))
            {
                var values=new Dictionary<Input,IOperand>();
                Input Canonical(Input input)=>template.Inputs.Single(p=>p.Parameter==input.Parameter && SamePath(p.Path,input.Path));
                bool Match(Expression pattern,IOperand actual,int depth=0,int readAt=-1)
                {
                    if(depth>16 || !Single(actual))return false;
                    if(pattern is Input input)
                    {
                        var key=Canonical(input);
                        // Post-SSA parameter/local storage can change between
                        // the original expression and allocation. Equal operand
                        // identity is not equal VALUE across such a write.
                        if(readAt>=0 && (actual is FieldReference
                            || actual is LocalVariable mutable && all.Skip(readAt+1).Take(index-readAt-1)
                                .Any(i=>ReferenceEquals(i.Destination,mutable))))return false;
                        if(!InlinedConstructorRecovery.AvailableBeforeAllocation(actual,method,all,index,home,ref dominance,aliases))return false;
                        if(values.TryGetValue(key,out var previous))return SameValue(previous,actual);
                        values[key]=actual;return true;
                    }
                    return pattern is Binary binary && actual is LocalVariable local
                        && definitions.TryGetValue(local,out var definition) && FloatOperation(definition)
                        && definition.OpCode==binary.Operation && all.IndexOf(definition)<index
                        && InlinedConstructorRecovery.AvailableBeforeAllocation(actual,method,all,index,home,ref dominance,aliases)
                        && Match(binary.Left,definition.Operands[1],depth+1,all.IndexOf(definition))
                        && Match(binary.Right,definition.Operands[2],depth+1,all.IndexOf(definition));
                }
                var valid=template.Stores.All(s=>stores.SingleOrDefault(i=>SamePath(Path((FieldReference)i.Operands[0]),s.Path)) is {} store
                    && Match(s.Value,store.Operands[1]));
                if(valid && template.Inputs.All(values.ContainsKey))matches.Add((template,values));
            }
            if(matches.Count==0)continue;
            if(matches.Count!=1)return false;
            var match=matches[0];var args=new List<IOperand>();var prep=new List<Instruction>();
            var serial=all.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
            for(var n=0;n<match.Template.Constructor.Parameters.Count;n++)
            {
                var parameterType=match.Template.Constructor.Parameters[n].ParameterType;
                var inputs=match.Template.Inputs.Where(p=>p.Parameter==n).ToArray();
                if(parameterType.FullName=="System.Single"){args.Add(match.Values[inputs.Single()]);continue;}
                var temp=new LocalVariable("reconstructedCtorArg"+serial,new Register(null,"ctor_arg_"+serial),parameterType);
                method.Locals.Add(temp);prep.Add(new(serial++,OpCode.Move,temp,new DefaultStructValue(parameterType)));
                foreach(var input in inputs)
                {
                    FieldReference? reference=null;
                    foreach(var part in input.Path)reference=new FieldReference(part,temp,part.Offset){Parent=reference};
                    prep.Add(new(serial++,OpCode.Move,reference!,match.Values[input]));
                }
                args.Add(temp);
            }
            home.Instructions.InsertRange(home.Instructions.IndexOf(allocation),prep);
            baseCall.SetOperands(new List<IOperand>{match.Template.Constructor,obj}.Concat(args).ToList());
            foreach(var store in stores){store.OpCode=OpCode.Nop;store.SetOperands();}
            return true;
        }
        return false;
    }
}
