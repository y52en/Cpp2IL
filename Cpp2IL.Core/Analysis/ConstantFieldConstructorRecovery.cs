using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Exact native templates for inlined parameterless field initializers. Unlike
// the trivial-ctor pass, every constant field write must match and is consumed.
public static class ConstantFieldConstructorRecovery
{
    public const string CacheKey="NativeConstantFieldConstructorTemplates";
    public enum ConstantKind { Integral,Single,Double }
    public sealed record Store(FieldAnalysisContext Field,long Value,int Width,ConstantKind Kind=ConstantKind.Integral);
    public sealed record Template(MethodAnalysisContext Constructor,IReadOnlyList<Store> Stores,
        MethodAnalysisContext? BaseConstructor=null,int BaseStoreIndex=-1);

    public static Template? Extract(MethodAnalysisContext constructor)
    {
        if(constructor.Name!=".ctor" || constructor.IsStatic || !constructor.IsVoid || constructor.Parameters.Count!=0
            || constructor.DeclaringType is not {IsValueType:false,GenericParameters.Count:0} owner
            || owner is GenericInstanceTypeAnalysisContext || owner.BaseType==null
            || constructor.ControlFlowGraph is not { } cfg)return null;
        var seen=new HashSet<Block>();var current=cfg.EntryBlock;var ordered=new List<Instruction>();
        while(seen.Add(current))
        {
            ordered.AddRange(current.Instructions);
            if(ReferenceEquals(current,cfg.ExitBlock))break;
            if(current.Successors.Count!=1)return null;
            current=current.Successors[0];
        }
        if(!ReferenceEquals(current,cfg.ExitBlock) || cfg.Blocks.Any(b=>!seen.Contains(b)))return null;
        var stores=new List<Store>();var baseSeen=false;var baseStoreIndex=-1;var returned=false;MethodAnalysisContext? baseConstructor=null;
        foreach(var instruction in ordered)
        {
            if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
            if(returned)return null;
            if(instruction is {OpCode:OpCode.Return,Operands.Count:0})
            {returned=true;continue;}
            if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                    Operands:[MethodAnalysisContext target,LocalVariable {IsThis:true}]}
                && ProvenDirectBase(owner,target) && !baseSeen)
            {baseSeen=true;baseStoreIndex=stores.Count;baseConstructor=target;continue;}
            if(instruction is not {OpCode:OpCode.Move,
                    Operands:[FieldReference {Parent:null,Local.IsThis:true} field,var value]}
                || !ReferenceEquals(field.Field.DeclaringType,owner) || field.Field.IsStatic
                || field.Offset!=field.Field.Offset || field.Offset<16
                || stores.Any(s=>ReferenceEquals(s.Field,field.Field))
                || Constant(field.Field.FieldType,value,instruction.NativeWriteSize) is not { } constant)return null;
            stores.Add(new(field.Field,constant.Value,instruction.NativeWriteSize,constant.Kind));
        }
        return baseSeen && returned && stores.Count>0 ? new(constructor,stores.ToArray(),baseConstructor,baseStoreIndex) : null;
    }

    private static (long Value,ConstantKind Kind)? Constant(TypeAnalysisContext type,IOperand value,int width)
        => value switch
        {
            Immediate integer when ExactIntegralWidth(type,width)=>(integer.Value,ConstantKind.Integral),
            FloatLiteral single when type.FullName=="System.Single" && width==4
                =>(System.BitConverter.SingleToInt32Bits(single.Value),ConstantKind.Single),
            DoubleLiteral wide when type.FullName=="System.Double" && width==8
                =>(System.BitConverter.DoubleToInt64Bits(wide.Value),ConstantKind.Double),
            _=>null
        };

    private static bool ProvenDirectBase(TypeAnalysisContext owner,MethodAnalysisContext target)
        => target.Name==".ctor" && !target.IsStatic && !target.IsVirtual && target.IsVoid
            && target.Parameters.Count==0 && TrivialConstructorRecovery.SameType(owner.BaseType,target.DeclaringType)
            && (target.DeclaringType?.FullName=="System.Object" ? IsObjectNoOp(target)
                :target.DeclaringType is {GenericParameters.Count:0,IsGenericInstance:false});

    private static bool ExactIntegralWidth(TypeAnalysisContext type,int width)
    {
        var scalar=type.IsEnumType ? type.EnumUnderlyingType : type;
        return width>0 && (scalar?.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte"=>1,
            "System.Char" or "System.Int16" or "System.UInt16"=>2,
            "System.Int32" or "System.UInt32"=>4,
            "System.Int64" or "System.UInt64"=>8,
            _=>0
        })==width;
    }

    private static bool IsObjectNoOp(MethodAnalysisContext target)=>target.Name==".ctor" && !target.IsStatic
        && target.IsVoid && target.Parameters.Count==0 && target.DeclaringType?.FullName=="System.Object"
        && target.GetExtraData<TrivialConstructorRecovery.ObjectProof>(TrivialConstructorRecovery.ObjectProofKey) is {IsNoOp:true};

    public static int Run(MethodAnalysisContext method)
    {
        if(method.ControlFlowGraph is not { } cfg)return 0;
        var count=0;
        foreach(var allocation in cfg.Instructions)
        {
            if(allocation is not {OpCode:OpCode.Newobj,Operands:[LocalVariable obj,TypeAnalysisContext type]}
                || type.GetExtraData<Template[]>(CacheKey) is not {Length:1} templates)continue;
            var template=templates[0];
            if(!ReferenceEquals(template.Constructor.DeclaringType,type))continue;
            var baseStoreIndex=template.BaseStoreIndex<0?template.Stores.Count:template.BaseStoreIndex;
            if(baseStoreIndex>template.Stores.Count)continue;
            var block=cfg.Blocks.Single(b=>b.Instructions.Contains(allocation));
            var at=block.Instructions.IndexOf(allocation)+1;var visited=new HashSet<Block>();
            var aliases=new HashSet<LocalVariable>{obj};var matched=new List<Instruction>();
            var failed=false;var complete=false;Instruction? baseCall=null;
            while(visited.Add(block) && !failed && !complete)
            {
                foreach(var instruction in block.Instructions.Skip(at))
                {
                    if(instruction.OpCode is OpCode.Nop or OpCode.Jump)continue;
                    if(instruction is {OpCode:OpCode.Move,Operands:[LocalVariable alias,LocalVariable source]} && aliases.Contains(source))
                    {aliases.Add(alias);continue;}
                    if(instruction is {OpCode:OpCode.CallVoid,NativeVirtualDispatch:false,
                            Operands:[MethodAnalysisContext target,LocalVariable receiver]}
                        && aliases.Contains(receiver)
                        && (template.BaseConstructor!=null?ReferenceEquals(target,template.BaseConstructor):IsObjectNoOp(target))
                        && baseCall==null && matched.Count==baseStoreIndex)
                    {
                        baseCall=instruction;
                        if(matched.Count==template.Stores.Count){complete=true;break;}
                        continue;
                    }
                    if(matched.Count==baseStoreIndex && baseCall==null
                        || matched.Count>=template.Stores.Count || instruction is not {OpCode:OpCode.Move,
                            Operands:[FieldReference {Parent:null} field,var value]}
                        || !aliases.Contains(field.Local)) {failed=true;break;}
                    var expected=template.Stores[matched.Count];
                    if(!ReferenceEquals(field.Field,expected.Field)
                        || Constant(field.Field.FieldType,value,instruction.NativeWriteSize) is not { } constant
                        || constant.Value!=expected.Value || constant.Kind!=expected.Kind
                        || field.Offset!=expected.Field.Offset
                        || instruction.NativeWriteSize!=expected.Width){failed=true;break;}
                    matched.Add(instruction);
                    if(baseCall!=null && matched.Count==template.Stores.Count){complete=true;break;}
                }
                if(complete || failed || block.Successors.Count!=1 || block.Successors[0].Predecessors.Count!=1)break;
                block=block.Successors[0];at=0;
            }
            // No prefix mutation on a mismatching post-base write/callback.
            // Replacing the exact base call with the original own constructor
            // preserves its before/between/after-store ordering internally.
            if(complete && baseCall!=null)
            {
                baseCall.SetOperand(0,template.Constructor);
                foreach(var store in matched){store.OpCode=OpCode.Nop;store.SetOperands();}
                count++;
            }
        }
        return count;
    }
}
