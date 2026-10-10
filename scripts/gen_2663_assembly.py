#!/usr/bin/env python3
"""Record-2663 part 2 generator: emits the entry-(0,3) membership assembly
support modules from the committed artifacts

  results/2663_bars.json        (190 per-panel 60-significant-digit bars,
                                 frozen sums LO_re/HI_re/LO_im/HI_im/CBAR)
  results/2663_budget_recon.json (barriers: reBarLo/reBarHi/imBarLo/imBarHi,
                                  rectangle endpoints reLo/reHi/imLo/imHi,
                                  checks)

and the committed Lean literals of `C1RouteACorrectionAnalyticIntervals2597.lean`
(the `analyticMomentInterval2597 0 3` fields are re-extracted verbatim).

Emits (all under ConnesWeilRH/Dev, LF newlines, deterministic):
  C1RouteAEntryBars2663.lean        bar literals, dispatchers, frozen sums,
                                    decide+kernel sum replays
  C1RouteAEntryRect2663.lean        rectangle literals, row ties, four
                                    strict-coordinate barriers
  C1RouteAEntryPanel2663B{00..09}   per-panel consumer facts (19 panels each)
  C1RouteAEntryPanels2663.lean      the five `forall k in Ico 0 190` facts

The hand-written assembly `C1RouteAEntryAssembly2663.lean` consumes these.

Entry scope (record 2664): with `--row=R --col=C` the same generator emits
the 13 modules into `ConnesWeilRH/Dev/OffDiagE{R:02d}_{C:02d}/` under
namespace `ConnesWeilRH.Dev.OffDiagE{R:02d}_{C:02d}`, reading

  results/2664_bars_{R}_{C}.json / results/2664_budget_recon_{R}_{C}.json

(recon_2663_budget.py --row=R --col=C) and re-extracting element `C` of the
`analyticMomentInterval2597_row_{R:02d}` literal, PLUS the two entry-scope
consumers rendered from the committed hand-written (0,3) texts by
assert-counted token substitution (`emit_entry_consumers`):

  C1RouteAEntryTiling2663.lean      the (R,C) tiling (node/width/column
                                    tokens and the Re(node) literal swapped;
                                    the `entryBetaBound2663` banner
                                    51923/10000 is column-3's and covers
                                    every |Re(node_R) * w_C^2| <= 51923/10000
                                    case at build time -- the rfl tie and
                                    norm_num close decide)
  C1RouteAEntryAssembly2663.lean    the (R,C) membership assembly

All bar comparisons are exact rationals; no float64 text enters any module.
Re-running this generator must reproduce every module byte-identically.
"""

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "ConnesWeilRH", "Dev")

# ---------------------------------------------------------------------------
# scope: legacy (0,3) lane, or an entry-scoped chain (--row=R --col=C)
# ---------------------------------------------------------------------------

args = sys.argv[1:]
row = col = None
for a in args:
    if a.startswith("--row="):
        row = int(a.split("=", 1)[1])
    elif a.startswith("--col="):
        col = int(a.split("=", 1)[1])
    else:
        raise SystemExit(f"unknown argument {a}")
if ((row is None) != (col is None)) or (row is not None and row == col):
    raise SystemExit("usage: gen_2663_assembly.py [--row=R --col=C]")
entry = row is not None
if not entry:
    row = 0  # docstring interpolation only; the extraction below pins row_00
    col = 3  # the committed (0,3) home lane
NS = ("ConnesWeilRH.Dev" if not entry
      else f"ConnesWeilRH.Dev.OffDiagE{row:02d}_{col:02d}")
OUTDIR = (DEV if not entry
          else os.path.join(DEV, f"OffDiagE{row:02d}_{col:02d}"))
BARS_SRC = (f"results/2664_bars_{row}_{col}.json" if entry
            else "results/2663_bars.json")
RECON_SRC = (f"results/2664_budget_recon_{row}_{col}.json" if entry
             else "results/2663_budget_recon.json")

OPEN_BLOCK = """open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
"""


def qlit(fstr):
    """Emit an exact rational literal as `((num : ℚ) / den)`."""
    num, den = fstr.split("/")
    return f"(({num} : ℚ) / {den})"


def read(name):
    with open(os.path.join(ROOT, name), encoding="utf-8") as fh:
        return fh.read()


def jread(name):
    with open(os.path.join(ROOT, "results", name), encoding="utf-8") as fh:
        return json.load(fh)


def write_module(fname, text):
    path = os.path.join(OUTDIR, fname)
    assert text.endswith("\n"), fname
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)
    return path


# ---------------------------------------------------------------------------
# inputs
# ---------------------------------------------------------------------------

bars = jread(f"2664_bars_{row}_{col}.json" if entry else "2663_bars.json")
recon = jread(f"2664_budget_recon_{row}_{col}.json" if entry
              else "2663_budget_recon.json")
panels = bars["panels"]
assert len(panels) == 190
# the list is emitted in k order; the tag is the 3-digit zero-padded index
for _idx, _p in enumerate(panels):
    _p["k"] = _idx
    assert _p["tag"] == f"{_idx:03d}", (_idx, _p["tag"])
sums = bars["sums"]
barriers = recon["barriers"]
assert all(barriers["checks"].values()), barriers["checks"]
assert recon["passes"] is True

# re-extract the (row, col) home rectangle fields verbatim from the committed
# row: element `col` of the `![...]` literal (fields 4*col .. 4*col+3 of 120)
intervals_src = read("ConnesWeilRH/Dev/C1RouteACorrectionAnalyticIntervals2597.lean")
rn = f"row_{row:02d}" if entry else "row_00"
m0 = re.search(r"noncomputable def analyticMomentInterval2597_" + rn +
               r"\b[^\n]*?:=\s*!\[", intervals_src)
assert m0, f"{rn} header not matched"
if entry and row == 29:
    # row_29 is the last row def; the end anchor is the umbrella def
    # (`analyticMomentInterval2597` with no `_row_` suffix)
    m1 = re.search(r"noncomputable def analyticMomentInterval2597\b",
                   intervals_src)
    assert m1, "umbrella def not matched after row_29"
else:
    nxt = row + 1 if entry else 1
    m1 = re.search(r"noncomputable def analyticMomentInterval2597_row_" +
                   f"{nxt:02d}" + r"\b", intervals_src)
    assert m1, f"row_{nxt:02d} header not matched after {rn}"
assert m1.start() > m0.end(), (rn, "end anchor before header")
elems = re.findall(r"\{[^{}]*\}", intervals_src[m0.end():m1.start()])
assert len(elems) == 30, len(elems)
quad = re.findall(
    r"(reLo|reHi|imLo|imHi) := \(\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)",
    elems[col])
assert [q[0] for q in quad] == ["reLo", "reHi", "imLo", "imHi"], quad
rect_src = {q[0]: (q[1], q[2]) for q in quad}
# consistency with the recon barrier block
for lbl, key in (("reLo", "reLo"), ("reHi", "reHi"),
                 ("imLo", "imLo"), ("imHi", "imHi")):
    assert f"{rect_src[lbl][0]}/{rect_src[lbl][1]}" == barriers[key], \
        (lbl, rect_src[lbl], barriers[key])

# frozen sums must be the exact sums of the literals (recon asserts this; re-check)
from fractions import Fraction as F  # noqa: E402
for key, ckey in (("LO_re", "reLo"), ("HI_re", "reHi"), ("LO_im", "imLo"),
                  ("HI_im", "imHi"), ("CBAR", "chBar")):
    tot = sum(F(p[ckey]) for p in panels)
    assert tot == F(sums[key]), (key, float(tot), float(F(sums[key])))

# ---------------------------------------------------------------------------
# Bars module
# ---------------------------------------------------------------------------

def emit_bars():
    L = []
    L.append(f"import {NS}.C1RouteAEntryTiling2663")
    L.append("")
    L.append(f"""\
/-! # Record 2663 part 2: bar literals, dispatchers and kernel sum replays

The 190-panel fenced bars of `{BARS_SRC}` (60 significant
digits), the per-`k` dispatchers the assembly consumes, and the frozen
sums `LOre/HIre/LOim/HIim/CBAR` replayed against the bar literals by
kernel `decide`.  All literals are exact rationals of the committed
ledger; no float64 text enters this file.

This module is generated by `scripts/gen_2663_assembly.py`; do not edit
by hand. -/
""")
    L.append("-- the per-panel literals are 60-significant-digit rationals; they")
    L.append("-- exceed the 100-character style limit by construction")
    L.append("set_option linter.style.longLine false")
    L.append("")
    L.append(OPEN_BLOCK)
    L.append(f"namespace {NS}")
    L.append("")
    L.append("""/-- The `k`-th centered entry panel: the record-2662 ball form's
integral over the halfwidth-`1/200` window centered at `entryCenter2663 k`. -/
noncomputable def entryPanel2663 (k : ℕ) : ℂ :=
  ∫ position in (-(1 / 200))..(1 / 200), entryF2663 (entryCenter2663 k + position)
""")
    L.append("/-! ## Per-panel bar literals -/")
    for p in panels:
        tag = p["tag"]
        L.append("")
        L.append(f"def reLoBar2663P{tag} : ℚ := {qlit(p['reLo'])}")
        L.append(f"def reHiBar2663P{tag} : ℚ := {qlit(p['reHi'])}")
        L.append(f"def imLoBar2663P{tag} : ℚ := {qlit(p['imLo'])}")
        L.append(f"def imHiBar2663P{tag} : ℚ := {qlit(p['imHi'])}")
        L.append(f"def chBar2663P{tag} : ℚ := {qlit(p['chBar'])}")
    L.append("")
    L.append("/-! ## Dispatchers -/")
    for name, desc in (("reLoBar2663", "the floor bar of the center's real part"),
                       ("reHiBar2663", "the ceil bar of the center's real part"),
                       ("imLoBar2663", "the floor bar of the center's imaginary part"),
                       ("imHiBar2663", "the ceil bar of the center's imaginary part"),
                       ("chBar2663", "the ceil bar of charge + residual")):
        L.append("")
        L.append(f"/-- `{name} k`: {desc} of panel `k`. -/")
        L.append(f"def {name} : ℕ → ℚ :=")
        L.append("  fun k => match k with")
        for p in panels:
            L.append(f"  | {p['k']} => {name}P{p['tag']}")
        L.append("  | _ => 0")
    L.append("")
    L.append("/-! ## Frozen sums (exact rationals of the bar literals) -/")
    for name, key in (("LOre2663", "LO_re"), ("HIre2663", "HI_re"),
                      ("LOim2663", "LO_im"), ("HIim2663", "HI_im"),
                      ("CBAR2663", "CBAR")):
        L.append("")
        L.append(f"def {name} : ℚ := {qlit(sums[key])}")
    L.append("")
    L.append("/-! ## Kernel sum replays -/")
    for thm, disp, frozen in (("sum_LOre2663", "reLoBar2663", "LOre2663"),
                              ("sum_HIre2663", "reHiBar2663", "HIre2663"),
                              ("sum_LOim2663", "imLoBar2663", "LOim2663"),
                              ("sum_HIim2663", "imHiBar2663", "HIim2663"),
                              ("sum_CBAR2663", "chBar2663", "CBAR2663")):
        L.append("")
        L.append("set_option maxHeartbeats 4000000 in")
        L.append("-- heartbeat budget for the kernel replay of the 190-arm dispatcher sum")
        L.append(f"/-- Kernel replay: the frozen sum of the `{disp}` literals. -/")
        L.append(f"theorem {thm} :")
        L.append(f"    (∑ k ∈ Finset.Ico 0 190, {disp} k) = {frozen} := by decide +kernel")
    L.append("")
    L.append("/-! ## Axiom audit -/")
    for thm in ("sum_LOre2663", "sum_HIre2663", "sum_LOim2663", "sum_HIim2663",
                "sum_CBAR2663"):
        L.append(f"#print axioms {thm}")
    L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# Rect module
# ---------------------------------------------------------------------------

def emit_rect():
    psi_zero = bool(recon.get("psi_zero"))
    psi_note = ("" if not psi_zero else

"  psi = 0 branch: this entry's phase cancels exactly (the record-2618\n"
"  exact-zero lane), so the two im barrier theorems emitted below are the\n"
"  0-based sign facts `(rectImLo2663 : Real) <= 0` and `0 <= rectImHi2663`\n"
"  that the membership chain consumes; the im bar literals and their\n"
"  compound ties above are still emitted (exact identities).\n\n")
    L = []
    L.append(f"import {NS}.C1RouteAEntryBars2663")
    L.append("import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticIntervals2597")
    L.append("")
    L.append(f"""\
/-! # Record 2663 part 2: home rectangle and the four barriers

The committed home rectangle `analyticMomentInterval2597 {row} {col}` (record
2597, row {row:02d} element {col}) as exact rational literals, the ties back to the
row fields, and the four strict-coordinate barrier facts the assembly
consumes:

  reBarLo = r3sq * (LOre - (CBAR + edgeBar)) >= reLo,
  reBarHi = r3sq * (HIre + (CBAR + edgeBar)) <= reHi,

and the im analogues (`edgeBar2663` is the two-edge banner of the frozen
tiling module; `r3sq = widthSq2663`).  All four hold exactly; the recon
`{RECON_SRC}` records the same rationals.

{psi_note}This module is generated by `scripts/gen_2663_assembly.py`; do not edit
by hand. -/
""")
    L.append("-- the rectangle literals are 90+-digit rationals; they exceed the")
    L.append("-- 100-character style limit by construction")
    L.append("set_option linter.style.longLine false")
    L.append("")
    L.append(OPEN_BLOCK)
    L.append(f"namespace {NS}")
    L.append("")
    L.append(f"/-! ## Home rectangle literals: `analyticMomentInterval2597 {row} {col}` -/")
    for lbl, name in (("reLo", "rectReLo2663"), ("reHi", "rectReHi2663"),
                      ("imLo", "rectImLo2663"), ("imHi", "rectImHi2663")):
        num, den = rect_src[lbl]
        L.append("")
        L.append(f"def {name} : ℚ := (({num} : ℚ) / {den})")
    L.append("")
    L.append("/-! ## Ties to the committed row -/")
    for lbl, name in (("reLo", "rectReLo2663"), ("reHi", "rectReHi2663"),
                      ("imLo", "rectImLo2663"), ("imHi", "rectImHi2663")):
        num, den = rect_src[lbl]
        L.append("")
        L.append(f"/-- The row field is the literal, by kernel reduction. -/")
        L.append(f"theorem {name}_tie2663 :")
        L.append(f"    (analyticMomentInterval2597 {row} {col}).{lbl} = ({name} : ℝ) := by")
        L.append(f"  rw [show (analyticMomentInterval2597 {row} {col}).{lbl} = (({num} : ℝ) / {den}) from rfl]")
        L.append(f"  norm_num [{name}]")
    L.append("")
    L.append("/-! ## Two-sided barriers -/")
    barlits = (("reBarLo2663", "reBarLo", "LOre2663 - (CBAR2663 + edgeBar2663)",
                "rectReLo2663"),
               ("reBarHi2663", "reBarHi", "HIre2663 + (CBAR2663 + edgeBar2663)",
                "rectReHi2663"),
               ("imBarLo2663", "imBarLo", "LOim2663 - (CBAR2663 + edgeBar2663)",
                "rectImLo2663"),
               ("imBarHi2663", "imBarHi", "HIim2663 + (CBAR2663 + edgeBar2663)",
                "rectImHi2663"))
    compound_defs = ("LOre2663", "HIre2663", "LOim2663", "HIim2663", "CBAR2663",
                     "edgeBar2663")
    for name, key, comp, rect in barlits:
        L.append("")
        L.append(f"def {name} : ℚ := {qlit(barriers[key])}")
    for name, key, comp, rect in barlits:
        unfolds = ", ".join([name] + [d for d in compound_defs if d in comp])
        L.append("")
        L.append("set_option exponentiation.threshold 400 in")
        L.append("-- the literal power `(1 / 2) ^ 302` sits in this goal; see the")
        L.append("-- tiling module")
        L.append("/-- Tie: the barrier literal is the compound quantity. -/")
        L.append(f"theorem {name}_tie2663 :")
        L.append(f"    {name} = widthSq2663 * ({comp}) := by")
        L.append(f"  rw [{unfolds}, widthSq2663]")
        L.append("  norm_num")
    # lower-side barriers: rect <= compound; upper-side: compound <= rect;
    # psi = 0 entries replace the two im barriers by the 0-based sign facts
    # the 2618 exact-zero membership chain consumes
    for name, key, comp, rect in barlits:
        side = "le" if "Lo" in name else "ge"
        L.append("")
        if psi_zero and "im" in name:
            if side == "le":
                L.append("/-- Barrier (psi = 0): the rectangle floor sits below zero. -/")
                L.append(f"theorem {rect}_{side}2663 :")
                L.append(f"    ({rect} : ℝ) ≤ 0 := by")
                L.append(f"  norm_num [{rect}]")
            else:
                L.append("/-- Barrier (psi = 0): zero sits below the rectangle ceil. -/")
                L.append(f"theorem {rect}_{side}2663 :")
                L.append(f"    (0 : ℝ) ≤ ({rect} : ℝ) := by")
                L.append(f"  norm_num [{rect}]")
            continue
        if side == "le":
            L.append("/-- Barrier: the rectangle floor sits below the compound bound. -/")
            L.append(f"theorem {rect}_{side}2663 :")
            L.append(f"    ({rect} : ℝ) ≤ ((widthSq2663 * ({comp}) : ℚ) : ℝ) := by")
            L.append(f"  rw [← {name}_tie2663]")
            L.append(f"  exact Rat.cast_le.mpr (by norm_num [{rect}, {name}])")
        else:
            L.append("/-- Barrier: the compound bound sits below the rectangle ceil. -/")
            L.append(f"theorem {rect}_{side}2663 :")
            L.append(f"    ((widthSq2663 * ({comp}) : ℚ) : ℝ) ≤ ({rect} : ℝ) := by")
            L.append(f"  rw [← {name}_tie2663]")
            L.append(f"  exact Rat.cast_le.mpr (by norm_num [{name}, {rect}])")
    L.append("")
    L.append("/-! ## Axiom audit -/")
    for lbl, name in (("reLo", "rectReLo2663"), ("reHi", "rectReHi2663"),
                      ("imLo", "rectImLo2663"), ("imHi", "rectImHi2663")):
        L.append(f"#print axioms {name}_tie2663")
    for name, key, comp, rect in barlits:
        L.append(f"#print axioms {name}_tie2663")
        side = "le" if "Lo" in name else "ge"
        L.append(f"#print axioms {rect}_{side}2663")
    L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# Batch modules: per-panel consumer facts
# ---------------------------------------------------------------------------

def panel_facts(p):
    k, tag = p["k"], p["tag"]
    # the legacy committed (0,3) lane kept tag 109 under its record-2649
    # name; the record-2664 entry chain renames every analytic module to the
    # 2656P{tag} spelling (verified in C1RouteAComplexPanelAnalytic2656P109)
    half_suffix = "2649" if (tag == "109" and not entry) else f"2656P{tag}"
    return f"""\
/-! ## Panel P{tag} (index {k}) -/

/-- Center tie: `entryCenter2663 {k}` is the record-2648 table center. -/
theorem entryCenterTie2663P{tag} :
    entryCenter2663 {k} = (complexPanelCenter2648P{tag} : ℝ) := by
  norm_num [entryCenter2663, complexPanelCenter2648P{tag}]

/-- Halfwidth tie: the panel halfwidth boils to `1/200`. -/
theorem entryHalfWidthTie2663P{tag} :
    complexPanelHalfWidthReal{half_suffix} = (1 / 200 : ℝ) := by
  rw [complexPanelHalfWidthReal{half_suffix}, complexPanelHalfWidth{half_suffix}]
  norm_num

/-- Charge-bar domination: the record-2662 charges are inside the bar. -/
theorem entryChargeBarTie2663P{tag} :
    (panelAssemblyCharge2662P{tag} : ℝ) + (panelResidualCharge2662P{tag} : ℝ)
      ≤ (chBar2663P{tag} : ℝ) := by
  rw [← Rat.cast_add]
  exact Rat.cast_le.mpr (by
    norm_num [panelAssemblyCharge2662P{tag}, panelResidualCharge2662P{tag},
      chBar2663P{tag}, ampValue2657P{tag}, ampRadius2657P{tag},
      phaseValue2658P{tag}, phaseRadius2658P{tag}, complexPanelIntegral2648P{tag},
      complexPanelResidualUpper2648P{tag}, deficitSq2662P{tag}, pairMagnitude2542])

/-- Center facts: the assembly-center pair in the four bar strips. -/
theorem entryCenterFact2663P{tag} :
    reLoBar2663P{tag} ≤ panelAssemblyCenter2662P{tag}.1
      ∧ panelAssemblyCenter2662P{tag}.1 ≤ reHiBar2663P{tag}
      ∧ imLoBar2663P{tag} ≤ panelAssemblyCenter2662P{tag}.2
      ∧ panelAssemblyCenter2662P{tag}.2 ≤ imHiBar2663P{tag} := by
  constructor
  · norm_num [reLoBar2663P{tag}, panelAssemblyCenter2662P{tag}, pairScale2542,
      pairMul2542, ampValue2657P{tag}, phaseValue2658P{tag}, complexPanelIntegral2648P{tag}]
  constructor
  · norm_num [reHiBar2663P{tag}, panelAssemblyCenter2662P{tag}, pairScale2542,
      pairMul2542, ampValue2657P{tag}, phaseValue2658P{tag}, complexPanelIntegral2648P{tag}]
  constructor
  · norm_num [imLoBar2663P{tag}, panelAssemblyCenter2662P{tag}, pairScale2542,
      pairMul2542, ampValue2657P{tag}, phaseValue2658P{tag}, complexPanelIntegral2648P{tag}]
  · norm_num [imHiBar2663P{tag}, panelAssemblyCenter2662P{tag}, pairScale2542,
      pairMul2542, ampValue2657P{tag}, phaseValue2658P{tag}, complexPanelIntegral2648P{tag}]

/-- The record-2662 L1 ball, transported to the entry panel: the panel
integral minus its assembly center is inside the charge bar. -/
theorem entryBallAt2663P{tag} :
    complexL12660 (entryPanel2663 {k} - embedPair2542 panelAssemblyCenter2662P{tag})
      ≤ (chBar2663P{tag} : ℝ) := by
  have h := panelTrueBall2662P{tag}
  rw [← entryCenterTie2663P{tag}, entryHalfWidthTie2663P{tag}] at h
  exact le_trans h (entryChargeBarTie2663P{tag})
"""


def emit_batch(idx):
    ks = list(range(idx * 19, idx * 19 + 19))
    tags = [panels[k]["tag"] for k in ks]
    L = []
    L.append(f"import {NS}.C1RouteAEntryBars2663")
    for tag in tags:
        L.append(f"import {NS}.C1RouteAPanelTrueBall2662P{tag}")
    L.append("")
    L.append(f"""\
/-! # Record 2663 part 2: per-panel consumer facts, batch {idx:02d}

Panels `{tags[0]}` .. `{tags[-1]}`: center and halfwidth ties, the
charge-bar domination, the four-conjunct rational center strip, and the
transport of the record-2662 L1 ball to the entry panel form.

This module is generated by `scripts/gen_2663_assembly.py`; do not edit
by hand. -/
""")
    L.append("-- the bar literals are 60-significant-digit rationals; they exceed the")
    L.append("-- 100-character style limit by construction")
    L.append("set_option linter.style.longLine false")
    L.append("")
    L.append(OPEN_BLOCK)
    L.append(f"namespace {NS}")
    L.append("")
    for k in ks:
        L.append(panel_facts(panels[k]))
    L.append("/-! ## Axiom audit (first panel of the batch) -/")
    first = tags[0]
    for thm in ("entryCenterTie2663P", "entryHalfWidthTie2663P",
                "entryChargeBarTie2663P", "entryCenterFact2663P",
                "entryBallAt2663P"):
        L.append(f"#print axioms {thm}{first}")
    L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# Panels module: the five forall-facts
# ---------------------------------------------------------------------------

def forall_theorem(name, doc, goal, acc, fact_suffix):
    L = []
    L.append(f"/-- {doc} -/")
    L.append(f"theorem {name} :")
    L.append(f"    ∀ k ∈ Finset.Ico 0 190,")
    L.append(f"      {goal} := by")
    L.append("  intro k hk")
    L.append("  have hk0 : 0 ≤ k := (Finset.mem_Ico.mp hk).1")
    L.append("  have hk1 : k < 190 := (Finset.mem_Ico.mp hk).2")
    L.append("  interval_cases k")
    for p in panels:
        k, tag = p["k"], p["tag"]
        L.append(f"  · simpa only [show panelAssemblyCenter2662Disp2663 {k} = panelAssemblyCenter2662P{tag} from rfl,")
        L.append(f"      show {acc[1]} {k} = {acc[1]}P{tag} from rfl] using entryCenterFact2663P{tag}{fact_suffix}")
    return "\n".join(L) + "\n"


def emit_panels():
    L = []
    for i in range(10):
        L.append(f"import {NS}.C1RouteAEntryPanel2663B{i:02d}")
    L.append("")
    L.append("""/-! # Record 2663 part 2: the uniform per-k consumer facts

The five `forall k in Ico 0 190` statements the assembly consumes: the
two center-strip directions per coordinate and the per-panel L1 ball
against the charge bar.  Each is proved by `interval_cases` over the
literal bars; the per-case facts are the batch-module theorems.

This module is generated by `scripts/gen_2663_assembly.py`; do not edit
by hand. -/
""")
    L.append("-- the per-case lines carry 60-significant-digit associativity chains;")
    L.append("-- they exceed the 100-character style limit by construction")
    L.append("set_option linter.style.longLine false")
    L.append("")
    L.append(OPEN_BLOCK)
    L.append(f"namespace {NS}")
    L.append("")
    L.append("""/-- `panelAssemblyCenter2662Disp2663 k`: the record-2662 assembly center
of panel `k`. -/
noncomputable def panelAssemblyCenter2662Disp2663 : ℕ → RatPair2542 :=
  fun k => match k with""")
    for p in panels:
        L.append(f"  | {p['k']} => panelAssemblyCenter2662P{p['tag']}")
    L.append("  | _ => (0, 0)")
    L.append("")
    for name, doc, goal, acc, suf in (
            ("entryPanelsCenterFstLo2663",
             "The real-part floor bars bound the assembly centers from below.",
             "reLoBar2663 k ≤ (panelAssemblyCenter2662Disp2663 k).1",
             ("", "reLoBar2663"), ".1"),
            ("entryPanelsCenterFstHi2663",
             "The real-part ceil bars bound the assembly centers from above.",
             "(panelAssemblyCenter2662Disp2663 k).1 ≤ reHiBar2663 k",
             ("", "reHiBar2663"), ".2.1"),
            ("entryPanelsCenterSndLo2663",
             "The imaginary-part floor bars bound the assembly centers from below.",
             "imLoBar2663 k ≤ (panelAssemblyCenter2662Disp2663 k).2",
             ("", "imLoBar2663"), ".2.2.1"),
            ("entryPanelsCenterSndHi2663",
             "The imaginary-part ceil bars bound the assembly centers from above.",
             "(panelAssemblyCenter2662Disp2663 k).2 ≤ imHiBar2663 k",
             ("", "imHiBar2663"), ".2.2.2")):
        L.append(forall_theorem(name, doc, goal, acc, suf))
        L.append("")
    # the ball fact has no bar-dispatch of the center in its goal
    L.append("""/-- The per-panel L1 ball against the charge bar, over the dispatcher. -/
theorem entryPanelsBall2663 :
    ∀ k ∈ Finset.Ico 0 190,
      complexL12660 (entryPanel2663 k - embedPair2542 (panelAssemblyCenter2662Disp2663 k))
        ≤ ((chBar2663 k : ℚ) : ℝ) := by
  intro k hk
  have hk0 : 0 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk1 : k < 190 := (Finset.mem_Ico.mp hk).2
  interval_cases k""")
    for p in panels:
        k, tag = p["k"], p["tag"]
        L.append(f"  · simpa only [show panelAssemblyCenter2662Disp2663 {k} = panelAssemblyCenter2662P{tag} from rfl,")
        L.append(f"      show chBar2663 {k} = chBar2663P{tag} from rfl] using entryBallAt2663P{tag}")
    L.append("")
    L.append("/-! ## Axiom audit -/")
    for name in ("entryPanelsCenterFstLo2663", "entryPanelsCenterFstHi2663",
                 "entryPanelsCenterSndLo2663", "entryPanelsCenterSndHi2663",
                 "entryPanelsBall2663"):
        L.append(f"#print axioms {name}")
    L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


# ---------------------------------------------------------------------------
# entry-scope consumers: the tiling and the assembly rendered from the
# committed hand-written (0,3) texts by assert-counted token substitution
# ---------------------------------------------------------------------------

def swap_counted(text, pairs, fname):
    """Apply (old, new, expected_count) swaps; a count mismatch is fatal."""
    for old, new, want in pairs:
        got = text.count(old)
        if got != want:
            raise SystemExit(
                f"{fname}: token {old!r} found {got} times, expected {want}")
        text = text.replace(old, new)
    for old, new, want in pairs:
        if old == new:
            continue
        # a paren-wrapping replacement legitimately contains its own old
        # spelling; anything beyond those sites is a stale token
        residual = want if old in new else 0
        got = text.count(old)
        assert got == residual, (fname, "stale token survives", old, got)
    return text


def emit_entry_consumers():
    assert entry, "entry consumers are entry-scope only"
    from math import isqrt
    from fractions import Fraction as Q
    import gen_2663_slots as S
    import offdiagonal_residual_pricing_2624 as P
    capture = json.loads(open(os.path.join(
        ROOT, "results", "2275_gap_owner_audit.json"),
        encoding="utf-8").read())["owner_capture"]
    pe = P.entry_parameters(capture, row, col)
    wsq = pe["radius"]                 # exact (width_col)^2
    node_re = pe["beta"] / wsq         # exact Re(node_row)
    # cross-bind the owner parameters to the committed artifacts and to the
    # on-disk entry trueball literal (the wave-1 wire tie, re-asserted)
    assert F(bars["r3sq"]) == wsq, (bars["r3sq"], wsq)
    assert F(recon["beta"]) == pe["beta"], (recon["beta"], pe["beta"])
    tb = open(os.path.join(OUTDIR, f"C1RouteAPanelTrueBall2662P000.lean"),
              encoding="utf-8").read()
    trow = S.rats(tb, f"nodeEntry{row}_2662P000")[0]
    assert trow == node_re, (trow, node_re)
    # width as an exact reduced fraction: wsq = (wnum/wden)^2 with w dyadic
    wnum, wden = isqrt(wsq.numerator), isqrt(wsq.denominator)
    assert wnum * wnum == wsq.numerator, wsq
    assert wden * wden == wsq.denominator, wsq
    assert Q(wnum, wden) ** 2 == wsq, (wnum, wden, wsq)
    # the emitted spellings must be the capture module's own spellings
    spell_node = f"(({node_re.numerator} : ℝ) / {node_re.denominator})"
    spell_wid = f"(({wnum} : ℝ) / {wden})"
    cap_src = read("ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean")
    assert spell_node in cap_src, spell_node
    assert spell_wid in cap_src, spell_wid

    til = read("ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean")
    til = swap_counted(til, [
        ("\nnamespace ConnesWeilRH.Dev\n", f"\nnamespace {NS}\n", 1),
        ("\nend ConnesWeilRH.Dev\n", f"\nend {NS}\n", 1),
        ("capturedNodes2584 0", f"capturedNodes2584 {row}", 8),
        ("capturedModulations2584 3", f"capturedModulations2584 {col}", 6),
        ("storedWidth 3", f"storedWidth {col}", 13),
        ("(4255901647865119 : ℝ) / 4503599627370496", spell_node, 1),
        ("(5224175567749775 : ℝ) / 2251799813685248", spell_wid, 2),
        ("(5224175567749775 / 2251799813685248) ^ 2",
         f"({wnum} / {wden}) ^ 2", 1),
        ("analyticMomentInterval2597 0 3",
         f"analyticMomentInterval2597 {row} {col}", 1),
        ("(0,3)", f"({row},{col})", 3),
        ("Re(node0)", f"Re(node{row})", 2),
        ("r3^2", f"r{col}^2", 2),
    ], "tiling")

    asm = read("ConnesWeilRH/Dev/C1RouteAEntryAssembly2663.lean")
    # The owner application `ownerMomentMatrix2351 capturedModulations2584
    # capturedNodes2584 0 3` carries its Fin indices TRAILING the vector
    # arguments -- a shape neither the attached `capturedModulations2584 3`
    # nor (for row = 0) the no-op `capturedNodes2584 0` swap can reach.  Swap
    # the full application FIRST (10 sites), which also removes those sites
    # from the attached `capturedNodes2584 0` count for row /= 0; the (29,3)
    # lane was blind to this only because col 3 IS the template's column.
    asm = swap_counted(asm, [
        ("\nnamespace ConnesWeilRH.Dev\n", f"\nnamespace {NS}\n", 1),
        ("\nend ConnesWeilRH.Dev\n", f"\nend {NS}\n", 1),
        ("import ConnesWeilRH.Dev.C1RouteAEntry",
         f"import {NS}.C1RouteAEntry", 3),
        ("ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3",
         f"ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 "
         f"{row} {col}", 10),
        ("capturedNodes2584 0", f"capturedNodes2584 {row}",
         29 if row == 0 else 19),
        ("capturedModulations2584 3", f"capturedModulations2584 {col}", 9),
        ("storedWidth 3", f"storedWidth {col}", 15),
        ("analyticMomentInterval2597 0 3",
         f"analyticMomentInterval2597 {row} {col}", 2),
        ("entry03Mem2663", f"entry{row:02d}{col:02d}Mem2663", 2),
        ("(0,3)", f"({row},{col})", 2),
        ("r3^2", f"r{col}^2", 1),
    ], "assembly")
    assert asm.count(
        f"ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 "
        f"{row} {col}") == 10, "ownerMomentMatrix index swap incomplete"

    if bool(recon.get("psi_zero")):
        # psi = 0 branch: the entry is exactly real (record-2618 phase
        # cancel).  Insert the phase-cancel pair before the membership
        # section, splice the two membership im clauses to the exact-zero
        # route, and extend the axiom audit.  Everything else -- including
        # entryImGe/Le2663, still true with the zero im bars -- is emitted
        # unchanged.
        anchor = "/-! ## Membership -/\n"
        assert asm.count(anchor) == 1, "membership anchor not found"
        insert = f"""\
/-- Phase cancellation at this entry: psi = 0 exactly. -/
theorem entryPhaseCancel2663 :
    (capturedNodes2584 {row}).im + capturedModulations2584 {col} = 0 := by
  norm_num [capturedNodes2584, capturedModulations2584]

/-- The owner entry is exactly real: the record-2618 phase-cancel theorem. -/
theorem entryImEqZero2663 :
    (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 {row} {col}).im = 0 := by
  rw [show ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 {row} {col}
      = momentEntry2351 capturedModulations2584 {col} (capturedNodes2584 {row}) from rfl]
  exact momentEntry2351_im_eq_zero_of_phase_cancel2618 _ _ _ entryPhaseCancel2663

"""
        asm = asm.replace(anchor, insert + anchor, 1)
        old_clauses = (
            "    le_trans (le_trans (le_of_eq rectImLo2663_tie2663)\n"
            "      rectImLo2663_le2663) entryImGe2663,\n"
            "    le_trans entryImLe2663\n"
            "      (le_trans rectImHi2663_ge2663 (le_of_eq rectImHi2663_tie2663.symm))⟩")
        new_clauses = (
            "    le_trans (le_trans (le_of_eq rectImLo2663_tie2663)\n"
            "      rectImLo2663_le2663) (le_of_eq entryImEqZero2663.symm),\n"
            "    le_trans (le_trans (le_of_eq entryImEqZero2663)\n"
            "      rectImHi2663_ge2663) (le_of_eq rectImHi2663_tie2663.symm)⟩")
        assert asm.count(old_clauses) == 1, "membership im clauses not matched"
        asm = asm.replace(old_clauses, new_clauses, 1)
        audit_anchor = "#print axioms entryImGe2663\n"
        assert asm.count(audit_anchor) == 1, "audit anchor not matched"
        asm = asm.replace(audit_anchor, audit_anchor
                          + "#print axioms entryPhaseCancel2663\n"
                          + "#print axioms entryImEqZero2663\n", 1)

    outs = [write_module("C1RouteAEntryTiling2663.lean", til),
            write_module("C1RouteAEntryAssembly2663.lean", asm)]
    print(f"entry consumers: node Re = {node_re}, width = {wnum}/{wden}")
    return outs


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    if entry and not os.path.isdir(OUTDIR):
        raise SystemExit(
            f"entry directory {os.path.relpath(OUTDIR, ROOT)} missing: run "
            f"gen_2664_entry.py --row={row} --col={col} --degree=D --emit "
            f"first (the assembly consumes the on-disk chain layout)")
    outs = []
    outs.append(write_module("C1RouteAEntryBars2663.lean", emit_bars()))
    outs.append(write_module("C1RouteAEntryRect2663.lean", emit_rect()))
    for i in range(10):
        outs.append(write_module(f"C1RouteAEntryPanel2663B{i:02d}.lean", emit_batch(i)))
    outs.append(write_module("C1RouteAEntryPanels2663.lean", emit_panels()))
    if entry:
        outs.extend(emit_entry_consumers())
    for path in outs:
        with open(path, "rb") as fh:
            data = fh.read()
        assert b"\r" not in data, path
        print(f"wrote {os.path.relpath(path, ROOT)} ({len(data)} bytes)")
    print(f"OK: {len(outs)} modules emitted under "
          f"{os.path.relpath(OUTDIR, ROOT)}; all literals from committed "
          f"artifacts only")
    return 0


if __name__ == "__main__":
    sys.exit(main())