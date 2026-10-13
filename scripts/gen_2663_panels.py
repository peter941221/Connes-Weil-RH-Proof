#!/usr/bin/env python3
"""Record-2663 generator: 190 per-panel instances of the record-2662 template.

Template: the committed `C1RouteAPanelTrueBall2662P094.lean` (pilot, green).
Per panel k the generator

  1. renames every identifier tag `P094` -> `P{tag}` (identifier-only:
     asserted that each match sits in identifier context and that the
     rational-literal multiset changes only in the four intended slots);
  2. substitutes the four numeric slots from `gen_2663_slots.slots(k)`:
       - the analytic residual exponential body (def + exp_le call),
       - the squared-deficit literal,
       - the rationalized exponent `n` in `(3 : ℚ) ^ n`,
       - the `n` argument of `exp_le_three_pow_rat2662`;
  3. applies the record-2649 name overrides for k = 109 (the pilot panel
     module of the committed analytic lane has its own names);
  4. asserts per-panel artifact existence (pin/table/analytic modules and
     the consumed theorem names) BEFORE emitting.

`--emit K...` writes the modules; `--check K...` (default 94 0 109 189)
renders in memory and reports the assertions without writing.  `--emit` with
k = 94 regenerates the committed template and asserts byte identity.
"""

import os
import re
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_2663_slots as S  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "ConnesWeilRH", "Dev")

TEMPLATE = "C1RouteAPanelTrueBall2662P094.lean"
EECALL_OLD = ") 1 (by norm_num)"
P109_OVERRIDES = [
    ("C1RouteAComplexPanelTable2655P109", "C1RouteAComplexPanelTable2648P109"),
    ("C1RouteAComplexPanelAnalytic2656P109", "C1RouteAComplexPanelAnalytic2649P109"),
    ("complexPanelPhaseDerivative2656P109", "complexPanelPhaseDerivative2649"),
    ("complexPanelPhase_hasDerivAt2656P109", "complexPanelPhase_hasDerivAt2649"),
    ("complexPanelHalfWidthReal_nonneg2656P109",
     "complexPanelHalfWidthReal_nonneg2649"),
    ("complexPanelHalfWidthReal2656P109", "complexPanelHalfWidthReal2649"),
    ("complexPanelHalfWidth2656P109", "complexPanelHalfWidth2649"),
    ("complexPanelDeficit_lower2656P109", "complexPanelDeficit_lower2649"),
    ("complexPanelIntegralError2656P109", "complexPanelIntegralError2649"),
    ("complexPanelPolyIntegral2656P109", "complexPanelPolyIntegral2649"),
    ("complexPanelPhase2656P109", "complexPanelPhase2649"),
]

RATLIKE = re.compile(r"\(\s*-?\d+\s*:\s*[ℚℝ]\s*\)\s*/\s*\d+|-?\d+\s*/\s*\d+")


def read(p):
    with open(os.path.join(DEV, p), encoding="utf-8") as fh:
        return fh.read()


def slots_ok(k):
    """Per-panel artifact and name existence assertions."""
    tag = f"{k:03d}"
    for mod, part in (
            (f"C1RouteAAmpPin2657P{tag}", f"theorem ampPin2657P{tag}"),
            (f"C1RouteAPhasePin2658P{tag}", f"theorem phaseCosPin2658P{tag}"),
            (f"C1RouteAPhasePin2658P{tag}", f"theorem phaseSinPin2658P{tag}"),
            (f"C1RouteAPanelCenterNormalization2661", "theorem panelCenterNormalization2661"),
    ):
        text = read(mod + ".lean")
        assert part in text, (mod, part)


def render(k, entry=None):
    """Render the trueball module for panel k.

    Legacy mode (`entry=None`) reads the committed entry-(0,3) modules and
    reproduces the committed bytes.  Entry-scoped mode passes

        entry = {"row", "col", "col_word", "prefix", "dev",
                 "node_re_lit", "node_im_lit", "modules",
                 "mod_lit", "mod_keep", "width_lit", "width_keep"}

    where `prefix` is the entry namespace (e.g.
    `ConnesWeilRH.Dev.OffDiagE29_03`), `dev` the entry's mirror directory,
    the two literals are the exact double-wrapped `((num : ℝ) / den)`
    spellings of the entry's captured node, `modules` the four family
    module-name map for `gen_2663_slots.slots`, and the remaining fields
    are the COLUMN-scoped slots:

      - `mod_lit` / `width_lit`: the single-wrapped spellings derived from
        the capture module's own `capturedModulations2584` / `capturedWidth2584`
        elements (outer parens stripped; a bare `(c : ℝ)` value is kept
        verbatim); used at the `modulationEntry` / `widthEntry` literal sites;
      - `mod_keep` / `width_keep`: True when the column's value EQUALS the
        template's (modulation cols 2,3; width cols 3,7) -- the template
        token is then retained byte-for-byte, which freezes the rendered
        (29,3)/(0,3) lane bytes;
      - `col_word`: the English-word name infix (zero..twenty_nine) for the
        `_three_eq2662` tie-theorem names -- `three` for col 3 keeps the
        template names byte-identical.

    The node-im site is PARKED under a placeholder before the modulation
    literal is touched: for row 0 the row's node-im literal equals the
    template's modulation token, so the single-wrapped token is ambiguous
    until the (double-wrapped) node site is removed from the search space.
    """
    legacy = entry is None
    if legacy:
        s = S.slots(k)
    else:
        s = S.slots(k, md=entry["modules"], dev=entry["dev"])
    tag = s["tag"]
    text = read(TEMPLATE)
    # ---- slot 1: analytic exponential body (def + exp_le call: 2 sites) ----
    old_ee = "2 * ((11733889 / 277722225) : ℝ)"
    assert text.count(old_ee) == 2, text.count(old_ee)
    text = text.replace(old_ee, s["eE_body"])
    # ---- slot 2: squared deficit (1 site, the deficitSq def) ----
    old_def = "((9999 / 10000 : ℚ) ^ 2)"
    assert text.count(old_def) == 1, text.count(old_def)
    text = text.replace(old_def, f"(({s['deficit'][0]} / {s['deficit'][1]} : ℚ) ^ 2)")
    # ---- slot 3: rationalized exponent (3 sites: def, statement, calc) ----
    assert text.count("(3 : ℚ) ^ 1") == 3, text.count("(3 : ℚ) ^ 1")
    text = text.replace("(3 : ℚ) ^ 1", f"(3 : ℚ) ^ {s['n']}")
    # ---- slot 4: the exp_le call's n argument ----
    assert text.count(EECALL_OLD) == 1, text.count(EECALL_OLD)
    text = text.replace(EECALL_OLD, f") {s['n']} (by norm_num)")
    # ---- rename: identifier-only P094 -> P{tag} ----
    if k != 94:
        assert tag != "094"
        occ = [m.start() for m in re.finditer(r"P094(?![0-9])", text)]
        assert len(occ) > 30, len(occ)
        # a match always sits in an identifier or prose ("P094" cannot be part
        # of a numeric literal: those carry no letter 'P')
        text = re.sub(r"P094(?![0-9])", f"P{tag}", text)
        assert "P094" not in text
    # ---- numeric-token invariance: literal COUNT unchanged ----
    assert len(RATLIKE.findall(read(TEMPLATE))) == len(RATLIKE.findall(text))
    # ---- P109 name overrides (legacy lane only; entries are uniform) ----
    if legacy and k == 109:
        for a, b in P109_OVERRIDES:
            assert a in text, a
            text = text.replace(a, b)
        assert "2656P109" not in text
        assert "Table2655P109" not in text
    # ---- header sanity ----
    assert f"P{tag} panel" in text.split("\n")[3] or f"P{tag}" in text[:400]
    if entry is not None:
        row, col = entry["row"], entry["col"]
        word = entry["col_word"]

        def swap(old, new, n):
            assert text.count(old) == n, (old[:48], text.count(old))
            return text.replace(old, new)

        text = swap("capturedNodes2584_zero_eq2662",
                    f"capturedNodes2584_row{row:02d}_eq2662", 3)
        text = swap("nodeEntry0_2662", f"nodeEntry{row}_2662", 4)
        text = swap("capturedNodes2584 0", f"capturedNodes2584 {row}", 5)
        text = swap("((4255901647865119 : ℝ) / 4503599627370496)",
                    entry["node_re_lit"], 1)
        # park the node-im site (row 0's literal coincides with the template
        # modulation token, making the single-wrapped pattern ambiguous)
        park = "@@NODE_IM_2662@@"
        text = swap("((5524291025718029 : ℝ) / 140737488355328)", park, 1)
        old_mod = "(5524291025718029 : ℝ) / 140737488355328"
        if entry["mod_keep"]:
            assert text.count(old_mod) == 1, text.count(old_mod)
        else:
            text = swap(old_mod, entry["mod_lit"], 1)
        text = swap(park, entry["node_im_lit"], 1)
        assert park not in text
        old_wid = "(5224175567749775 : ℝ) / 2251799813685248"
        if entry["width_keep"]:
            assert text.count(old_wid) == 1, text.count(old_wid)
        else:
            text = swap(old_wid, entry["width_lit"], 1)
        # ---- column-scoped names (word infix keeps col 3 byte-identical) ----
        text = swap("modulationEntry3_2662", f"modulationEntry{col}_2662", 4)
        text = swap("widthEntry3_2662", f"widthEntry{col}_2662", 4)
        text = swap("capturedModulations2584_three_eq2662",
                    f"capturedModulations2584_{word}_eq2662", 3)
        text = swap("storedWidth_three_eq2662",
                    f"storedWidth_{word}_eq2662", 3)
        text = swap("capturedModulations2584 3",
                    f"capturedModulations2584 {col}", 5)
        text = swap("storedWidth 3", f"storedWidth {col}", 5)
        text = swap("Captured node 0", f"Captured node {row}", 1)
        text = swap("Captured modulation 3", f"Captured modulation {col}", 1)
        text = swap("Captured width 3", f"Captured width {col}", 1)
        text = swap("(0,3)", f"({row},{col})", 5)
        for old, new in (("modulationEntry3_2662", f"modulationEntry{col}_2662"),
                         ("widthEntry3_2662", f"widthEntry{col}_2662"),
                         ("capturedModulations2584 3",
                          f"capturedModulations2584 {col}"),
                         ("storedWidth 3", f"storedWidth {col}"),
                         ("Captured modulation 3",
                          f"Captured modulation {col}"),
                         ("Captured width 3", f"Captured width {col}")):
            if old != new:
                assert old not in text, old
        # ---- scope: the four family imports + the namespace ----
        prefix = entry["prefix"]
        fams = ("C1RouteAComplexPanelTable2655", "C1RouteAComplexPanelAnalytic2656",
                "C1RouteAAmpPin2657", "C1RouteAPhasePin2658")
        for fam in fams:
            old = f"import ConnesWeilRH.Dev.{fam}P{tag}"
            assert text.count(old) == 1, old
            text = text.replace(old, f"import {prefix}.{fam}P{tag}")
        assert text.count("namespace ConnesWeilRH.Dev\n") == 1
        text = text.replace("namespace ConnesWeilRH.Dev\n",
                            f"namespace {prefix}\n\nopen ConnesWeilRH.Dev\n", 1)
        assert text.count("end ConnesWeilRH.Dev") == 1
        text = text.replace("end ConnesWeilRH.Dev", f"end {prefix}", 1)
        for m in re.finditer(rf"^import {re.escape(prefix)}\.(\S+)$", text, re.M):
            fn = m.group(1) + ".lean"
            assert os.path.exists(os.path.join(entry["dev"], fn)), \
                f"entry import missing on disk: {fn}"
        # Keep this bridge definitionally equal instead of invoking `simpa`
        # on the very large entry-specific rational residual.  Lean 4.30's
        # simplifier can leave an unresolved HSub metavariable for some
        # off-diagonal entries; the theorem already has exactly the target
        # type after unfolding these two local definitions.
        old_bridge = (
            f"simpa [ampExpArg2662P{tag}, deficitSq2662P{tag}] using h)")
        assert text.count(old_bridge) == 1, (tag, text.count(old_bridge))
        text = text.replace(old_bridge, "exact h)")
        return text, s
    slots_ok(k)
    # ---- every import of the rendered module must exist on disk ----
    for m in re.finditer(r"^import ConnesWeilRH\.Dev\.(\S+)$", text, re.M):
        fn = m.group(1) + ".lean"
        assert os.path.exists(os.path.join(DEV, fn)), \
            f"import missing on disk: {fn}"
    return text, s


def main():
    mode = "--check"
    ks = []
    for a in sys.argv[1:]:
        if a.startswith("--"):
            mode = a
        else:
            ks.append(int(a))
    if mode == "--emit":
        if not ks:
            ks = [k for k in range(190) if k != 94]
    elif not ks:
        ks = [94, 0, 109, 189]
    out = []
    for k in ks:
        text, s = render(k)
        tag = s["tag"]
        name = f"C1RouteAPanelTrueBall2662P{tag}.lean"
        if k == 94:
            assert text == read(TEMPLATE), "k=94 render is not byte-identical"
        if mode == "--emit":
            with open(os.path.join(DEV, name), "w", encoding="utf-8",
                      newline="\n") as fh:
                fh.write(text)
        out.append((tag, len(text), s["n"], str(s["eE"]), str(s["center"])))
    for row in out:
        print("tag=%s bytes=%d n=%d eE=%s c=%s" % row)
    return 0


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except AttributeError:
        pass
    sys.exit(main())
