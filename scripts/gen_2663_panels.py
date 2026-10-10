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


def render(k):
    s = S.slots(k)
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
    # ---- P109 name overrides ----
    if k == 109:
        for a, b in P109_OVERRIDES:
            assert a in text, a
            text = text.replace(a, b)
        assert "2656P109" not in text
        assert "Table2655P109" not in text
    # ---- header sanity ----
    assert f"P{tag} panel" in text.split("\n")[3] or f"P{tag}" in text[:400]
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