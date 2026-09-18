#!/usr/bin/env python3
"""Minimal DVI text extractor with math-font rendering (prose + formulas).

Built for the 1631/1632 rounds (base weapon inventory): the primary sources of
the BM/Toeplitz-kernel criteria are DVI files (Poltoratski's page), and both the
exact hypotheses of the criterion at p = 2 and the quantitative Hilbert
transform lemmas of the 2005 chapter have to be read off the *formulas*.

The extractor walks the DVI opcode stream, tracks the current font through
fnt_def/fnt_num/fnt1-4, and renders:

  * text fonts  (cmr/cmbx/cmti/cmss/cmtt/cmcsc/cmu) -- ASCII glyphs;
  * math fonts  (cmmi/cmmib math italic, cmsy/cmbsy symbols, cmex large
    symbols) -- through explicit glyph tables (see GLYPHS below).  Math italic
    stores Latin letters at their ASCII codes and Greek letters in codes 0-39,
    so the tables are pinned to that layout; unknown codes are skipped rather
    than guessed.

Vertical moves are classified by size, not by opcode family alone:

  * |move| > VMOVE_NEWLINE * font size  -> line break (TeX uses `down`/`y` with
    the baselineskip for new lines);
  * smaller moves on sub/superscript opcodes (`z`) -> `_` (down) / `^` (up)
    markers, which is what TeX emits around exponents and indices.

That last rule is what makes formulas readable (`L^1(dPi)`, `h_0`), and it is
why the extractor can be used to read hypotheses off a formula-bearing source.

TWO OPCODE TABLES.  The retrieved files are DVI version 2 (preamble `i` = 2)
and their control-opcode numbering differs from the classic table used by
version-1 files: reading the post amble gives the byte offset of the last
`bop`, and the bytes just before it are `... pop pop pop eop bop`, which pins
the version-2 block at bop = 139, eop = 140, push = 141, pop = 142 (classic:
135/136/137/138).  The parser tries both tables and keeps the extraction with
more text, so a version-1 file is handled without a flag.

Usage:  python scripts/dvi_extract.py <file.dvi> <out.txt> [--pages A-B]
"""

import sys

MATH_FONT_MARKERS = ("cmmi", "cmsy", "cmex", "msam", "msbm", "eufm", "cmmib", "cmbsy")
TEXT_FONT_MARKERS = ("cmr", "cmbx", "cmti", "cmss", "cmtt", "cmcsc", "cmu")
SPACE_MOVE = 0.14          # fraction of the font's scaled size
VMOVE_NEWLINE = 0.7        # fraction of the font's scaled size

# opcode families, as (bop, eop, push, pop, right1, w0, x0, down1, y0, z0, fnt_num0)
TABLE_V2 = (139, 140, 141, 142, 143, 147, 152, 157, 161, 166, 171)
TABLE_V1 = (135, 136, 137, 138, 139, 143, 148, 153, 157, 162, 167)


def _cm_layout():
    """Computer Modern math-italic glyph layout (cmmi / cmmib).

    Codes 0-10 uppercase Greek, 11-39 lowercase Greek and the six variants,
    Latin letters at their ASCII codes (this is why \\mathcode`a = "7161 in
    plain.tex), plus the handful of named symbols plain.tex places by hand.
    """
    t = {}
    upper = "ΓΔΘΛΞΠΣΥΦΨΩ"
    lower = "αβγδεζηθικλμνξπρστυφχψω"
    for i, ch in enumerate(upper):
        t[i] = ch
    for i, ch in enumerate(lower):
        t[11 + i] = ch
    t.update({34: "ε", 35: "ϑ", 36: "ϖ", 37: "ϱ", 38: "ς", 39: "ϕ"})
    t.update({48: "′", 49: "∞", 60: "ℜ", 61: "ℑ", 64: "∂", 92: "∠",
              96: "ℓ", 123: "ı", 124: "ȷ", 125: "℘"})
    for c in list(range(65, 91)) + list(range(97, 123)):
        t[c] = chr(c)
    for c in ".,:;()[]!?+-=*/<>'\"|":
        t[ord(c)] = c
    for c in range(48, 58):
        t[c] = chr(c)
    return t


def _cm_symbols():
    """Computer Modern math symbols (cmsy / cmbsy).

    Pinned on LaTeX's fontmath.ltx declarations ("14 = \\leq, "32 = \\in,
    "6A = \\vert, ...) rather than on a full font listing; the 0x40-0x5B block
    (alternate delimiters) is left unmapped on purpose, only \\angle ("5C) and
    the delimiters from "62 up are included.
    """
    ops = "−⋅×∗÷⋄±∓⊕⊖⊗⊘⊙◯∘∙"
    rel1 = "≍≡⊆⊇≤≥⪯⪰∼≈⊂⊃≪≫≺≻"
    arrows1 = "←→↑↓↔↗↘≃⇐⇒⇔↦↩↪⇀⇁⇌∞"
    misc = "∈∋△▽◁▷∀∃¬∅ℜℑ⊤⊥"
    t = {}
    for i, ch in enumerate(ops + rel1 + arrows1 + misc):
        t[i] = ch
    t.update({92: "∠", 98: "⌊", 99: "⌋", 100: "⌈", 101: "⌉",
              102: "{", 103: "}", 104: "⟨", 105: "⟩", 106: "|", 107: "‖",
              108: "↕", 109: "⇕", 110: "\\", 112: "√",
              124: "♣", 125: "♢", 126: "♡", 127: "♠"})
    return t


def _cm_large():
    """Computer Modern large symbols (cmex).

    TeX's extensible delimiters live at 0-15 ("0 = ( ... "0F = ]), the large
    operators at "30-"60; only the ones that occur in analysis formulas are
    mapped (integral, sums, unions/intersections).
    """
    t = {0: "(", 1: ")", 2: "[", 3: "]", 8: "{", 9: "}",
         10: "⟨", 11: "⟩", 12: "⌊", 13: "⌋", 14: "⌈", 15: "⌉"}
    t.update({72: "∮", 74: "⊙", 76: "⊕", 78: "⊗", 80: "∑", 81: "∏",
              82: "∫", 84: "⋂", 86: "⋃", 88: "⨆", 90: "⋁", 92: "⋀",
              94: "⨄", 96: "∐"})
    return t


CMMI = _cm_layout()
CMSY = _cm_symbols()
CMEX = _cm_large()

# family marker (first match wins) -> glyph table
FONT_TABLES = (
    (("cmmi", "cmmib"), CMMI),       # math italic (bold shares the layout)
    (("cmsy", "cmbsy"), CMSY),       # math symbols
    (("cmex",), CMEX),               # large symbols
)


def table_for(name):
    low = name.lower()
    for markers, table in FONT_TABLES:
        if any(m in low for m in markers):
            return table
    return None


def is_text_font(name):
    low = name.lower()
    return any(m in low for m in TEXT_FONT_MARKERS) and not any(
        m in low for m in MATH_FONT_MARKERS)


def _ams_blackboard():
    """AMS blackboard bold (msbm): letters keep their ASCII codes, so the
    table maps them to the Unicode double-struck characters (that is how
    \\mathbb{R} becomes readable instead of vanishing)."""
    t = {}
    special = {65: "𝔸", 66: "𝔹", 67: "ℂ", 68: "𝔻", 69: "𝔼", 70: "𝔽",
               71: "𝔾", 72: "ℍ", 73: "𝕀", 74: "𝕁", 75: "𝕂", 76: "𝕃",
               77: "𝕄", 78: "ℕ", 79: "𝕆", 80: "ℙ", 81: "ℚ", 82: "ℝ",
               83: "𝕊", 84: "𝕋", 85: "𝕌", 86: "𝕍", 87: "𝕎", 88: "𝕏",
               89: "𝕐", 90: "ℤ"}
    t.update(special)
    for c in range(97, 123):
        t[c] = chr(0x1D552 + c - 97)
    for c in range(48, 58):
        t[c] = chr(0x1D7D8 + c - 48)
    return t


MSBM = _ams_blackboard()

# family marker (first match wins) -> glyph table
FONT_TABLES = (
    (("cmmi", "cmmib"), CMMI),       # math italic (bold shares the layout)
    (("cmsy", "cmbsy"), CMSY),       # math symbols
    (("cmex",), CMEX),               # large symbols
    (("msbm",), MSBM),               # blackboard bold
)


def scan_fonts(data):
    """Collect every font definition in the file.

    TeX writes a fnt_def only the FIRST time a font is used -- in practice all
    of them inside page 1 -- so a page parsed in isolation has an empty font
    table and emits nothing.  Scanning the whole file for fnt_def records and
    seeding every page with the result is what makes page-wise parsing work.
    The record layout is fixed (num, checksum, scale, design size, name), and
    the name is validated as printable ASCII, so a byte-pattern hit inside
    glyph data is rejected.
    """
    fonts = {}
    for p in range(len(data)):
        c = data[p]
        if not 243 <= c <= 246:
            continue
        k = c - 242
        if p + 1 + k + 14 > len(data):
            continue
        num = int.from_bytes(data[p + 1:p + 1 + k], "big")
        if num > 255:
            continue
        q = p + 1 + k + 12
        a, l = data[q], data[q + 1]
        if not (1 <= a + l <= 20):
            continue
        name = data[q + 2:q + 2 + a + l]
        if not all(48 <= b <= 122 and chr(b).isalnum() for b in name):
            continue
        scale = int.from_bytes(data[p + 1 + k + 4:p + 1 + k + 8], "big")
        fonts[num] = (name.decode("ascii"), max(scale, 1))
    return fonts


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


def parse_pages(data, table, pages=None):
    """Parse page by page inside TRUE page bounds.

    Each page runs from its `bop` (skipping the 45 header bytes) to the next
    `bop`; the last one ends at the postamble.  Parsing a page to end-of-file
    instead would let one desynchronised byte swallow everything after it, and
    would duplicate every page once per chunk.
    """
    bop = table[0]
    offs = bop_offsets(data, bop)
    if not offs:
        return parse(data, table)
    post = data.rfind(bytes([248]))
    if post < offs[-1]:
        post = len(data)
    bounds = offs + [post]
    lo, hi = pages if pages else (1, len(offs))
    seed = scan_fonts(data)
    chunks = []
    for k in range(len(offs)):
        if not (lo <= k + 1 <= hi):
            continue
        try:
            chunks.append(parse(data[bounds[k] + 45:bounds[k + 1]],
                                table, single_page=True, fonts=seed))
        except (IndexError, ValueError):
            chunks.append("")
    return "".join(chunks)


def parse(data, table, single_page=False, fonts=None):
    bop, eop, push, pop, right1, w0, x0, down1, y0, z0, fnum0 = table
    out = []
    fonts = {} if fonts is None else fonts   # font number -> (name, scaled size)
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
            wval = w_or_x[0]
            if k:
                wval = int.from_bytes(data[i:i + k], "big", signed=True)
                i += k
            move = wval
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
            k = c - down1 + 1
            move = int.from_bytes(data[i:i + k], "big", signed=True)
            i += k
            _vmove(out, fonts, cur, move)
        elif y0 <= c <= y0 + 4:                         # y0..y4
            k = c - y0
            move = int.from_bytes(data[i:i + k], "big", signed=True) if k else 0
            i += k
            _vmove(out, fonts, cur, move)
        elif z0 <= c <= z0 + 4:                         # z0..z4  (sub/superscripts)
            k = c - z0
            move = int.from_bytes(data[i:i + k], "big", signed=True) if k else 0
            i += k
            _script(out, fonts, cur, move)
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
    if not (is_text_font(name) or table_for(name)):
        return
    if move > SPACE_MOVE * cur[1]:
        out.append(" ")


def _vmove(out, fonts, cur, move):
    """Real vertical move: a line break when it is at least a fraction of an em."""
    if abs(move) > VMOVE_NEWLINE * cur[1]:
        out.append("\n")


def _script(out, fonts, cur, move):
    """Sub/superscript displacement (TeX's `z` moves do not disturb v)."""
    if move > 0.05 * cur[1]:
        out.append("_")
    elif move < -0.05 * cur[1]:
        out.append("^")


def _emit(out, fonts, cur, code):
    name, _ = fonts.get(cur[0], ("", 1))
    table = table_for(name)
    if table is not None:
        ch = table.get(code)
        if ch:
            out.append(ch)
        return
    if not is_text_font(name):
        return
    if 32 <= code < 127:
        out.append(chr(code))


def score(text):
    return sum(1 for ch in text if ch.isalpha())


def parse_args(argv):
    src, dst, pages = None, None, None
    i = 1
    while i < len(argv):
        a = argv[i]
        if a == "--pages":
            i += 1
            lo, _, hi = argv[i].partition("-")
            pages = (int(lo), int(hi) if hi else int(lo))
        elif src is None:
            src = a
        elif dst is None:
            dst = a
        i += 1
    return src, dst, pages


def main():
    src, dst, pages = parse_args(sys.argv)
    if not src or not dst:
        print(__doc__)
        return 2
    data = open(src, "rb").read()
    best, best_table = "", None
    for table in (TABLE_V2, TABLE_V1):
        text = parse_pages(data, table, pages)
        if score(text) > score(best):
            best, best_table = text, table
    with open(dst, "w", encoding="utf-8") as fh:
        fh.write(best)
    print("wrote %s (%d bytes, %d letters, table bop=%d, pages=%s)"
          % (dst, len(best), score(best), (best_table or TABLE_V2)[0], pages or "all"))
    return 0


if __name__ == "__main__":
    sys.exit(main())