#!/usr/bin/env python3
"""Minimal DVI text extractor: prose only, formulas dropped.

Built for the 1631 round (base weapon inventory): the primary source of the
BM/Toeplitz-kernel criteria is a DVI file (Poltoratski's page), and the exact
hypotheses of the criterion at p = 2 have to be read off the prose.

The extractor walks the DVI opcode stream, tracks the current font through
fnt_def/fnt_num/fnt1-4, emits glyphs for text fonts only (Computer Modern
Roman / slanted / bold / typewriter; math italic and symbol fonts are skipped
because their glyph codes are not text), emits a space on a horizontal move
larger than a fraction of the font's scaled size, and a newline on a vertical
move.  `xxx` specials are skipped.

TWO OPCODE TABLES.  The retrieved file is DVI version 2 (preamble `i` = 2) and
its control-opcode numbering differs from the classic table used by version-1
files: reading the post amble gives the byte offset of the last `bop`, and the
bytes just before it are `... pop pop pop eop bop`, which pins the version-2
block at bop = 139, eop = 140, push = 141, pop = 142 (classic: 135/136/137/138).
The parser therefore tries both tables and keeps the extraction with more text
(the wrong table desynchronises within a page and yields almost nothing), so a
version-1 file is handled without a flag.

Usage:  python scripts/dvi_extract.py <file.dvi> <out.txt>
"""

import sys

MATH_FONT_MARKERS = ("cmmi", "cmsy", "cmex", "msam", "msbm", "eufm", "cmmib", "cmbsy")
TEXT_FONT_MARKERS = ("cmr", "cmbx", "cmti", "cmss", "cmtt", "cmcsc", "cmu")
SPACE_MOVE = 0.18          # fraction of the font's scaled size

# opcode families, as (bop, eop, push, pop, right1, w0, x0, down1, y0, z0, fnt_num0)
TABLE_V2 = (139, 140, 141, 142, 143, 147, 152, 157, 161, 166, 171)
TABLE_V1 = (135, 136, 137, 138, 139, 143, 148, 153, 157, 162, 167)


def bop_offsets(data, bop=139):
    """Offsets of page starts: `bop` followed by ten 4-byte params whose last
    eight are zero.  Parsing page-by-page keeps a local desynchronisation from
    destroying the rest of the file."""
    offs, pat = [], data.find(bytes([bop]), 0)
    while pat >= 0:
        if data[pat + 9:pat + 41] == bytes(32):
            offs.append(pat)
        pat = data.find(bytes([bop]), pat + 1)
    return offs


def parse_pages(data, table):
    bop = table[0]
    offs = bop_offsets(data, bop)
    if not offs:
        return parse(data, table)
    post = data.rfind(bytes([248]))
    if post < offs[-1]:
        post = len(data)
    chunks = []
    for a in offs:
        try:
            chunks.append(parse(data[a + 45:post], table, single_page=True))
        except (IndexError, ValueError):
            chunks.append("")
    return "".join(chunks)
    

def parse(data, table, single_page=False):
    bop, eop, push, pop, right1, w0, x0, down1, y0, z0, fnum0 = table
    out = []
    fonts = {}                      # font number -> (name, scaled size)
    cur = (0, 1)
    stack = []
    w_or_x = [0, 0]                 # last w and x move (TeX reuses them)
    i, n = 0, len(data)
    while i < n:
        c = data[i]
        i += 1
        if c <= 127:                                    # set_char
            _emit(out, fonts, cur, c)
        elif c <= 131:                                  # set1..set4
            k = c - 127
            code = int.from_bytes(data[i:i + k], "big")
            i += k
            _emit(out, fonts, cur, code)
        elif c <= 133:                                  # set_rule / put_rule
            i += (c - 131) + 4
        elif c == 134:                                  # nop
            pass
        elif c == bop:
            i += 44
        elif c == eop:
            out.append("\n")
        elif c == push:
            stack.append(cur)
        elif c == pop:
            if stack:
                cur = stack.pop()
        elif right1 <= c <= right1 + 3:                 # right1..right4
            k = c - right1 + 1
            move = int.from_bytes(data[i:i + k], "big", signed=True)
            i += k
            _space(out, fonts, cur, move)
        elif w0 <= c <= w0 + 4:                         # w0..w4
            k = c - w0
            if k:
                wval = int.from_bytes(data[i:i + k], "big", signed=True)
                i += k
            move = wval if k else w_or_x[0]
            _space(out, fonts, cur, move)
            w_or_x[0] = move
        elif x0 <= c <= x0 + 4:                         # x0..x4
            k = c - x0
            if k:
                xval = int.from_bytes(data[i:i + k], "big", signed=True)
                i += k
                w_or_x[1] = xval
            _space(out, fonts, cur, w_or_x[1])
        elif down1 <= c <= down1 + 3:                   # down1..down4
            i += c - down1 + 1
            out.append("\n")
        elif y0 <= c <= y0 + 4:                         # y0..y4
            i += c - y0
        elif z0 <= c <= z0 + 4:                         # z0..z4
            i += c - z0
        elif fnum0 <= c <= 234:                         # fnt_num_0..63
            num = c - fnum0
            cur = (num, fonts.get(num, ("", 1))[1])
        elif 235 <= c <= 238:                           # fnt1..fnt4
            k = c - 234
            num = int.from_bytes(data[i:i + k], "big")
            i += k
            cur = (num, fonts.get(num, ("", 1))[1])
        elif 239 <= c <= 242:                           # xxx1..xxx4
            k = c - 238
            length = int.from_bytes(data[i:i + k], "big")
            i += k + length
        elif 243 <= c <= 246:                           # fnt_def1..4
            k = c - 242
            num = int.from_bytes(data[i:i + k], "big")
            i += k
            i += 4                                      # checksum
            scale = int.from_bytes(data[i:i + 4], "big")
            i += 4 + 4                                  # scale, design size
            a, l = data[i], data[i + 1]
            i += 2
            name = data[i:i + a + l].decode("latin1", "replace")
            i += a + l
            fonts[num] = (name, max(scale, 1))
            cur = (num, fonts[num][1])
        elif c == 247 and not single_page:              # pre
            i += 1 + 4 + 4 + 4                          # i, num, den, mag
            k4 = int.from_bytes(data[i:i + 4], "big")
            if 0 < k4 < (1 << 20):
                i += 4 + k4                             # k + comment (with a, l)
            else:
                i += 1 + data[i]                        # version-2: 1-byte k
        elif c == 248:                                  # post
            i += 4 * 6 + 2 + 2
        elif c == 249:                                  # post_post
            i = n
        else:
            pass
    return "".join(out)


def _space(out, fonts, cur, move):
    name, _ = fonts.get(cur[0], ("", 1))
    low = name.lower()
    if not any(m in low for m in TEXT_FONT_MARKERS):
        return
    if move > SPACE_MOVE * cur[1]:
        out.append(" ")


def _emit(out, fonts, cur, code):
    name, _ = fonts.get(cur[0], ("", 1))
    low = name.lower()
    if any(m in low for m in MATH_FONT_MARKERS):
        return
    if not any(m in low for m in TEXT_FONT_MARKERS):
        return
    if 32 <= code < 127:
        out.append(chr(code))


def score(text):
    return sum(1 for ch in text if ch.isalpha())


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    data = open(sys.argv[1], "rb").read()
    best, best_table = "", None
    for table in (TABLE_V2, TABLE_V1):
        text = parse_pages(data, table)
        if score(text) > score(best):
            best, best_table = text, table
    with open(sys.argv[2], "w", encoding="utf-8") as fh:
        fh.write(best)
    print("wrote %s (%d bytes, %d letters, table bop=%d)"
          % (sys.argv[2], len(best), score(best), best_table[0]))
    return 0


if __name__ == "__main__":
    sys.exit(main())