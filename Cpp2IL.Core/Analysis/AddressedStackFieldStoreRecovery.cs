using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Normalize exact scalar stores into already-proven aggregate stack storage
// BEFORE SSA/DCE can discard independently named sibling slots. The existing
// metadata resolver subsequently binds [aggregate+offset] to the actual field.
// No guessed layouts, inferred struct types or synthesized initialization.
public static class AddressedStackFieldStoreRecovery
{
    public static int Run(MethodAnalysisContext method)
        =>method.AppContext.InstructionSet is Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet
            && method.AppContext.Binary.PointerSizeBytes==8 ? Recover(method.ControlFlowGraph!):0;

    internal static int Recover(ISILControlFlowGraph graph)
        =>Recover(graph,[]);

    internal static int Recover(ISILControlFlowGraph graph,IEnumerable<(Register Slot,TypeAnalysisContext Type)> contracts)
    {
        var roots=graph.Instructions.Where(i=>i is {OpCode:OpCode.Move,Operands:[Register,DefaultStructValue]})
            .Select(i=>(Slot:(Register)i.Operands[0],Type:((DefaultStructValue)i.Operands[1]).Type))
            .Concat(contracts)
            .Where(x=>Offset(x.Slot,out _) && x.Type.IsValueType && !x.Type.HasAnyGenericParameters()
                && !TypeSizes.IsScalarValueType(x.Type)
                && graph.Instructions.Any(i=>i.Operands.Any(o=>o is AddressOf {Target:Register slot} && slot.Number==x.Slot.Number)))
            .GroupBy(x=>x.Slot.Name).Where(g=>g.Select(x=>x.Type).Distinct().Count()==1)
            .Select(g=>g.First()).ToArray();
        var changed=0;
        var serial=graph.Instructions.Select(i=>i.Index).DefaultIfEmpty(0).Max()+1;
        foreach(var block in graph.Blocks)
        for(var index=0;index<block.Instructions.Count;index++)
        {
            var instruction=block.Instructions[index];
            if(instruction is not {OpCode:OpCode.Move,Operands:[Register slot,var value],NativeWriteSize:1 or 2 or 4 or 8 or 16}
                || value is not (Register or Immediate or FloatLiteral or DoubleLiteral)
                || !Offset(slot,out var written))continue;
            var matches=new List<(Register Root,List<Piece> Pieces)>();
            foreach(var root in roots)
            {
                if(!Offset(root.Slot,out var basis))continue;
                var delta=(long)written-basis;
                if(delta<0 || delta>int.MaxValue
                    || (root.Type.Attributes&System.Reflection.TypeAttributes.LayoutMask)==System.Reflection.TypeAttributes.ExplicitLayout)
                    continue;
                var proof=new LocalVariable("layout-proof",root.Slot,root.Type);
                var resolved=ConstantAt(block,index,value);
                var pieces=new List<Piece>();var cursor=0;
                while(cursor<instruction.NativeWriteSize)
                {
                    Piece? piece=null;
                    foreach(var width in new[]{8,4,2,1})
                    {
                        if(width>instruction.NativeWriteSize-cursor)continue;
                        var field=NestedFieldAccess.Find(root.Type,proof,delta+cursor,width)?.Field;
                        if(field==null || !TypeSizes.IsScalarValueType(field.FieldType)
                            || TypeSizes.UnboxedSize(field.FieldType,8)!=width)continue;
                        IOperand? part=null;
                        if(resolved is Immediate bits)
                        {
                            // A 128-bit zero has unambiguous zero high lanes;
                            // nonzero constants beyond a single native word do not.
                            if(instruction.NativeWriteSize<=8 || bits.Value==0)
                                part=Decode(bits,width,cursor,field.FieldType);
                        }
                        else if(cursor==0 && width==instruction.NativeWriteSize)
                        {
                            if(field.FieldType.FullName is not ("System.Single" or "System.Double")
                                || value is FloatLiteral or DoubleLiteral
                                || value is Register reg && reg.Name.StartsWith("V",StringComparison.Ordinal))part=value;
                        }
                        if(part!=null){piece=new(delta+cursor,width,part);break;}
                    }
                    if(piece==null)break;
                    pieces.Add(piece);cursor+=piece.Width;
                }
                if(cursor==instruction.NativeWriteSize)matches.Add((root.Slot,pieces));
            }
            if(matches.Count!=1)continue;
            var match=matches[0];var first=match.Pieces[0];
            instruction.SetOperands(new MemoryOperand(match.Root,addend:first.Offset),first.Value);
            instruction.NativeWriteSize=first.Width;instruction.NativeZeroSize=0;
            var more=match.Pieces.Skip(1).Select(piece=>new Instruction(serial++,OpCode.Move,
                new MemoryOperand(match.Root,addend:piece.Offset),piece.Value){NativeWriteSize=piece.Width}).ToArray();
            block.Instructions.InsertRange(index+1,more);index+=more.Length;
            changed++;
        }
        return changed;
    }

    private sealed record Piece(long Offset,int Width,IOperand Value);

    private static IOperand ConstantAt(Block block,int before,IOperand value)
    {
        var seen=new HashSet<string>();
        while(value is Register register && seen.Add(register.Name) && seen.Count<=8)
        {
            var found=false;
            for(var i=before-1;i>=0;i--)
            {
                var instruction=block.Instructions[i];
                if(instruction.IsCall || instruction.OpCode is OpCode.IndirectCall or OpCode.Invalid or OpCode.NotImplemented)return value;
                if(instruction.Destination is not Register written || written.Name!=register.Name)continue;
                // ARM64 materializes small constants as ORR with the zero
                // register. This range is identical at either 32 or 64 bits.
                if(instruction is {OpCode:OpCode.Or,Operands:[_,Immediate {Value:0},Immediate {Value:>=0 and <=int.MaxValue} literal]})return literal;
                if(instruction is not {OpCode:OpCode.Move,Operands:[_,Register or Immediate]})return value;
                value=instruction.Operands[1];before=i;found=true;break;
            }
            if(!found)break;
        }
        return value;
    }

    private static IOperand? Decode(Immediate value,int width,int offset,TypeAnalysisContext fieldType)
    {
        var type=fieldType.IsEnumType?fieldType.EnumUnderlyingType:fieldType;
        if(type==null)return null;
        var bits=value.Value==0?0UL:(value.UnsignedValue>>(offset*8))&(ulong.MaxValue>>((8-width)*8));
        return type.FullName switch
        {
            "System.Boolean" when bits<=1=>new Immediate((long)bits),
            "System.SByte"=>new Immediate(unchecked((sbyte)bits)),
            "System.Int16"=>new Immediate(unchecked((short)bits)),
            "System.Int32"=>new Immediate(unchecked((int)bits)),
            "System.Byte" or "System.Char" or "System.UInt16" or "System.UInt32" or "System.Int64" or "System.UInt64"
                or "System.IntPtr" or "System.UIntPtr"=>new Immediate(unchecked((long)bits)),
            "System.Single" when bits==0=>new FloatLiteral(0),
            "System.Double" when bits==0=>new DoubleLiteral(0),
            _=>null
        };
    }

    private static bool Offset(Register slot,out int offset)
    {
        offset=0;if(!slot.Name.StartsWith("stack_",StringComparison.Ordinal))return false;
        var text=slot.Name.Substring(6);var negative=text.StartsWith("-",StringComparison.Ordinal);
        if(negative)text=text.Substring(1);
        if(!int.TryParse(text,NumberStyles.AllowHexSpecifier,CultureInfo.InvariantCulture,out var value)||value<0)return false;
        offset=negative?-value:value;return true;
    }
}
