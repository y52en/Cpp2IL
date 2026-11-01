using System;
using System.Collections.Generic;
using System.Linq;

namespace LibCpp2IL.Elf;

// ELF64 little-endian .eh_frame, DW_EH_PE_pcrel | DW_EH_PE_sdata4.
// Unknown CIE encodings are skipped. Malformed records never yield partial
// bounds. Frame rules are not interpreted: only their exact function extent.
public static class ElfEhFrameBounds
{
    static uint U32(byte[] bytes, int at) => BitConverter.ToUInt32(bytes, at);
    static bool Leb(byte[] bytes, ref int at, int end, out ulong value)
    {
        value = 0;
        for (var shift = 0; shift < 70 && at < end; shift += 7)
        {
            var next = bytes[at++];
            if (shift == 63 && (next & 0x7e) != 0) return false;
            value |= (ulong)(next & 127) << shift;
            if ((next & 128) == 0) return true;
        }
        return false;
    }

    static bool SkipLeb(byte[] bytes, ref int at, int end)
    {
        for (var n = 0; n < 10 && at < end; n++) if ((bytes[at++] & 128) == 0) return true;
        return false;
    }

    static bool SkipEncoded(byte[] bytes, ref int at, int end, byte encoding)
    {
        if (encoding == 0xff || (encoding & 0x70) == 0x50) return false;
        var size = (encoding & 15) switch { 0 or 4 or 12 => 8, 2 or 10 => 2, 3 or 11 => 4, _ => 0 };
        if ((encoding & 15) is 1 or 9) return SkipLeb(bytes, ref at, end);
        if (size == 0 || at > end - size) return false;
        at += size; return true;
    }

    static byte? Cie(byte[] bytes, int at, int end)
    {
        if (at >= end || bytes[at++] != 1) return null;
        var start = at;
        while (at < end && bytes[at] != 0 && at - start < 32) at++;
        if (at == end || at - start >= 32 || at == start || bytes[start] != (byte)'z') return null;
        var augmentation = System.Text.Encoding.ASCII.GetString(bytes, start, at - start); at++;
        if (!Leb(bytes, ref at, end, out var alignment) || alignment == 0 || !SkipLeb(bytes, ref at, end)
            || at >= end || bytes[at++] != 30 || !Leb(bytes, ref at, end, out var size)
            || size > (ulong)(end - at)) return null;
        var augmentationEnd = at + (int)size; byte? encoding = null;
        foreach (var letter in augmentation.Skip(1))
        {
            if (letter == 'S') continue;
            if (at >= augmentationEnd) return null;
            var value = bytes[at++];
            if (letter == 'R') { if (encoding != null) return null; encoding = value; }
            else if (letter == 'L') { }
            else if (letter != 'P' || !SkipEncoded(bytes, ref at, augmentationEnd, value)) return null;
        }
        return at == augmentationEnd ? encoding : null;
    }

    public static Dictionary<ulong, int> Read(byte[] bytes, int offset, int size, ulong virtualAddress)
    {
        var empty = new Dictionary<ulong, int>();
        if (offset < 0 || size < 0 || offset > bytes.Length - size || virtualAddress > ulong.MaxValue - (ulong)size) return empty;
        var end = offset + size; var at = offset;
        var cies = new Dictionary<int, byte?>(); var ranges = new List<(ulong Start, int Length)>();
        while (at < end)
        {
            if (at > end - 4) return empty;
            var length = U32(bytes, at);
            if (length == 0)
            {
                for (var p = at; p < end; p++) if (bytes[p] != 0) return empty;
                break;
            }
            if (length == uint.MaxValue || length < 4 || length > end - at - 4) return empty;
            var finish = at + 4 + (int)length; var id = U32(bytes, at + 4);
            if (id == 0) cies[at] = Cie(bytes, at + 8, finish);
            else
            {
                if (id > (uint)(at + 4 - offset)) return empty;
                var cie = at + 4 - (int)id;
                if (!cies.TryGetValue(cie, out var encoding)) return empty;
                if (encoding == 0x1b)
                {
                    if (length < 13) return empty;
                    var displacement = unchecked((int)U32(bytes, at + 8));
                    var pc = virtualAddress + (ulong)(at + 8 - offset);
                    if (displacement < 0 && pc < (ulong)-(long)displacement
                        || displacement >= 0 && pc > ulong.MaxValue - (ulong)displacement) return empty;
                    var address = displacement < 0 ? pc - (ulong)-(long)displacement : pc + (ulong)displacement;
                    var count = unchecked((int)U32(bytes, at + 12));
                    var augmentationAt = at + 16;
                    if (count <= 0 || count % 4 != 0 || address == 0 || address % 4 != 0
                        || address > ulong.MaxValue - (ulong)count
                        || !Leb(bytes, ref augmentationAt, finish, out var augmentationSize)
                        || augmentationSize > (ulong)(finish - augmentationAt)) return empty;
                    ranges.Add((address, count));
                }
            }
            at = finish;
        }
        // Conflicting/overlapping ranges cannot identify one complete body.
        var ordered = ranges.OrderBy(r => r.Start).ToArray(); var invalid = new HashSet<ulong>();
        ulong furthestEnd = 0; ulong furthestOwner = 0;
        foreach (var row in ordered)
        {
            if (row.Start < furthestEnd) { invalid.Add(row.Start); invalid.Add(furthestOwner); }
            var stop = row.Start + (ulong)row.Length;
            if (stop > furthestEnd) { furthestEnd = stop; furthestOwner = row.Start; }
        }
        return ordered.Where(r => !invalid.Contains(r.Start)).ToDictionary(r => r.Start, r => r.Length);
    }
}
