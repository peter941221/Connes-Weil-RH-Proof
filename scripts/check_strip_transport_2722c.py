"""Record 2722C checker: strip-envelope transport tie and guards.

Sections
  A  transcription guards on C1StripTransport2722C.lean: the cardinal
     sum spelled from record-1958 `laplaceAt_correction`, the wired
     strip-point / weight / threshold spellings verbatim, the variant
     binders hNorm/hIm/hvanish/hsupport/hgate24/hprefix byte-identical
     to the record-2721C parent;
  B  numeric tie of the three pins against the committed record-2720
     artifact row B, in exact Fraction arithmetic on the stored
     decimal/float renders;
  C  tail extension: the 2720 envelope scan stops at TAIL_T = 600 while
     the wired pins quantify over ALL t.  This section re-runs the
     pointwise-valid envelope formula (same constants, same D table,
     same 1.05 tail law) over t in [600, 1e7] for both rows' channels
     and both signs, reports the maximum weighted envelope and the
     monotone-decrease evidence at the end of the range, and compares
     against both the artifact certified constant and the wired pin;
  D  mutation controls (feasibility-checked per AGENTS 2ah): a pin
     below the certified render must fail B, a wrong weight exponent
     must fail A, a perturbed gate binder must fail the parent-diff.

Usage: python3 scripts/check_strip_transport_2722c.py [--smoke]
Writes results/2722c_strip_transport_tie.json.
"""

import hashlib
import importlib.util
import json
import os
import re
import sys
import time
from fractions import Fraction

import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SMOKE = "--smoke" in sys.argv
T_START = time.time()

LEAN = os.path.join(ROOT, "ConnesWeilRH", "Dev", "C1StripTransport2722C.lean")
LEAN_1958 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                         "C1ExplicitFiniteNodeCorrection.lean")
LEAN_2721 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                         "C1FourPointRowBWired2721.lean")
ART2720 = os.path.join(ROOT, "results", "2720_p3_certified_strip_constants.json")
OUT = os.path.join(ROOT, "results", "2722c_strip_transport_tie.json")

# wired pins (must match the Lean defs verbatim)
WQ = Fraction(26, 10 ** 17)
WC4 = 61000000
WC2 = 29000000

failures = []
checks = {}


def sha(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def txt(p):
    with open(p, encoding="utf-8") as fh:
        return fh.read()


def guard(name, ok, detail=""):
    checks[name] = bool(ok)
    if not ok:
        failures.append((name, detail))
    print(("PASS " if ok else "FAIL ") + name + (" " + detail if detail else ""))


src = txt(LEAN)
src1958 = txt(LEAN_1958)
src2721 = txt(LEAN_2721)

# ---------------------------------------------------------------------------
# A: transcription guards
# ---------------------------------------------------------------------------

# A1: the identification theorem is exactly record-1958 laplaceAt_correction
# (capture the full spaced call -- `\S+` could never equal it; smoke-found fix)
m = re.search(
    r"theorem laplaceAt_cardinalOwner[\s\S]*?:=\s*"
    r"([A-Za-z_][\w. ]*)", src)
guard("A1_identification_call",
      m is not None and m.group(1) == "laplaceAt_correction nodes seed y s",
      "captured %r" % (m.group(1) if m else None))

# A2: cardinalSum body equals the RHS of laplaceAt_correction (1958 file),
# compared as whitespace-insensitive token streams.
mrhs = re.search(
    r"theorem laplaceAt_correction.*?laplaceAt \(correction nodes seed y\) s =\n?\s*"
    r"(∑ z ∈ nodes.*?) := by", src1958, re.S)
mmine = re.search(r"def cardinalSum.*?ℂ :=\n(.*?)\n\n", src, re.S)
assert mrhs is not None, "A2: laplaceAt_correction RHS not found in 1958 source"
assert mmine is not None, "A2: cardinalSum body not found in 2722C source"
rhs = mrhs.group(1)
mine = mmine.group(1)
norm = lambda s: re.sub(r"\s+", "", s)
guard("A2_cardinalSum_verbatim", norm(mine) == norm(rhs))

# A3: wired spellings verbatim in the transport lemmas
STRIP_POINT = "((sigma : Complex) + (t : Complex) * Complex.I)"
# counts measured on the compiled-good source (hypothesis + conclusion
# per lemma, plus one pin each in the variant): 3 lemmas x 2 + variant x 3
for frag, cnt in [
    (STRIP_POINT, 9),
    ("64 ≤ |t| →", 3),
    ("‖t / (2 * Real.pi)‖ ^ 4", 3),
    ("‖t / (2 * Real.pi)‖ ^ 2", 3),
    ("wiredQRowB2721", 3),
    ("wiredC4RowB2721", 3),
    ("wiredC2RowB2721", 3),
    ("Set.Icc (0 : Real) 1", 9),
]:
    guard("A3_spelling_%s" % frag[:28], src.count(frag) == cnt,
          "count %d != %d" % (src.count(frag), cnt) if src.count(frag) != cnt else "")

# A3m: mutation control -- the ^ 3 spelling must be ABSENT (feasibility:
# a copy with ^ 4 -> ^ 3 in the quartic lemma would fire A3).
guard("A3m_no_cubic_weight", src.count("‖t / (2 * Real.pi)‖ ^ 3") == 0)

# A4: variant structural binders byte-identical to the 2721C parent.
def binder_block(text, start_marker, end_marker):
    i = text.index(start_marker)
    j = text.index(end_marker, i)
    return norm(text[i:j])

parent_variant = src2721[src2721.index(
    "theorem fourPointContradictionRowBWired2721C"):]
mine_variant = src[src.index("theorem fourPointContradictionRowBWired2722C"):]
for nm, marker, pendm, mendm in [
    ("hNorm", "(hNorm :", "(hIm :", "(hIm :"),
    ("hIm", "(hIm :", "(hvanish :", "(hvanish :"),
    ("hvanish", "(hvanish :", "(hsupport :", "(hsupport :"),
    # hsupport: the parent's next binder is the black-box hcontract, the
    # variant's is the new identification hbase -- the guarded region is
    # only the hsupport binder itself, so the end marker is per-file.
    ("hsupport", "(hsupport :", "(hcontract :", "(hbase :"),
    ("hgate24", "(hgate24 :", "(hprefix :", "(hprefix :"),
    # hprefix: the parent closes in term mode ("False :="), the variant in
    # tactic mode ("False := by"); "False" itself never occurs inside the
    # binder text, so it is the sound shared terminator.
    ("hprefix", "(hprefix :", "False", "False"),
]:
    a = binder_block(parent_variant, marker, pendm)
    b = binder_block(mine_variant, marker, mendm)
    guard("A4_binder_%s" % nm, a == b)
# A4m: feasibility control for the hgate24 guard -- perturbing the copy
# (24 -> 25) must make it differ.
bad = mine_variant.replace("(hgate24 : ICgate", "(hgate24 : ICgateX", 1)
guard("A4m_gate_guard_fires",
      binder_block(bad, "(hgate24 :", "(hprefix :")
      != binder_block(parent_variant, "(hgate24 :", "(hprefix :"))

# A5: the variant calls the 2721C parent with exactly three transported
# slots and the pin-derived proofs.
guard("A5_parent_call",
      "refine fourPointContradictionRowBWired2721C base correction rho "
      "hNorm hIm\n      hvanish hsupport ?_ ?_ ?_ hgate24 hprefix" in src)

# ---------------------------------------------------------------------------
# B: numeric tie against the committed 2720 artifact (row B)
# ---------------------------------------------------------------------------
art = json.load(open(ART2720, encoding="utf-8"))
rowB = art["rows"][1]
assert rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5
cert = rowB["certified"]
c4s = cert["C4_star"]
c2s = cert["C2_star_corr"]
q64 = cert["q_star_T64"]

def fr(x):
    return Fraction(x)

tie = {
    "C4_star": c4s, "C4_pin": WC4, "C4_margin": WC4 - c4s,
    "C2_star": c2s, "C2_pin": WC2, "C2_margin": WC2 - c2s,
    "q_star_T64": q64, "q_pin": float(WQ),
    "q_margin": float(WQ - fr(q64)),
}
guard("B1_C4_tie", fr(q64) >= 0 and fr(c4s) <= fr(WC4))
guard("B2_C2_tie", fr(c2s) <= fr(WC2))
guard("B3_q_tie", fr(q64) <= WQ)
guard("B4_positive_q", fr(q64) > 0)

# ---------------------------------------------------------------------------
# C: tail extension beyond TAIL_T = 600 (same engine, same constants)
# ---------------------------------------------------------------------------
spec = importlib.util.spec_from_file_location(
    "p3_2720", os.path.join(ROOT, "scripts",
                            "p3_certified_strip_constants_2720.py"))
assert spec is not None and spec.loader is not None, "p3_2720 loader unavailable"
p3 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p3)

row = p3.Row_(p3.CANDIDATES[1])
cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)
D, ctl = p3.certified_D_table()
guard("C0_D_table_controls", ctl[1] and ctl[2])

# anchor: reproduce the committed renders in the same run
sup_b, C4rep = p3.scan_channel(cb, 4, D)
sup_c, C2rep = p3.scan_channel(cc, 2, D)
q64rep = p3.q_star_at(cb, 64, D)
rel = lambda a, b: abs(a - b) / max(abs(b), 1e-300)
checks["C1_anchor_rel"] = {
    "C4": rel(C4rep, c4s), "C2": rel(C2rep, c2s), "q": rel(q64rep, q64)}
guard("C1_anchor_C4", rel(C4rep, c4s) <= 1e-12)
guard("C1_anchor_C2", rel(C2rep, c2s) <= 1e-12)
guard("C1_anchor_q", rel(q64rep, q64) <= 1e-12)

# extension cells t in [600, T_MAX] with the 1.05 law (both signs)
T0 = float(p3.TAIL_T)
TMAX = 800.0 if SMOKE else 1.0e7
def extend(consts, weight_p):
    t = T0
    mx = mp.mpf(0)
    vals = []
    while t < TMAX:
        t2 = min(t * 1.05, TMAX)
        v = mp.mpf(0)
        for sgn in (1, -1):
            _, vw = p3.cell_val(consts, float(t), float(t2), D, weight_p, sgn)
            v = max(v, vw)
        vals.append(v)
        mx = max(mx, v)
        t = t2
    return mx, vals

ext = {}
for nm, consts, wp, star, pin in [
    ("base_quartic", cb, 4, c4s, WC4),
    ("corr_quadratic", cc, 2, c2s, WC2),
    ("base_contract", cb, 0, q64, float(WQ)),
]:
    mx, vals = extend(consts, wp)
    # DECREASING-TAIL EVIDENCE, mp-native.  Full-run restructure (disclosed
    # per the anchor law): the previous float64 rendering of the last cells
    # underflowed to 0.0 for the base channels (envelope decays like
    # t^m * tau^-120, so past ~160 cells the values sit near 1e-1100) and
    # `0.0 < 0.0` read as a plateau.  The invariant is strict decrease in
    # the engine's own mpmath precision; the floats are display only.
    # Consecutive per-cell ratios are representable (t^(-113)-scale, ~1e-4)
    # and double as the underflow-proof evidence.
    tail5 = vals[-6:]
    dec = all(tail5[i + 1] < tail5[i] for i in range(len(tail5) - 1))
    ratios = [float(tail5[i + 1] / tail5[i]) for i in range(len(tail5) - 1)]
    assert all(r > 0 for r in ratios), "mp ratio display underflow"
    ratio_pin = float(mx) / pin if pin > 0 else float("inf")
    ext[nm] = {
        "range": [T0, TMAX],
        "cells": len(vals),
        "max_weighted_envelope": float(mx),
        "vs_artifact_star": float(mx) / star,
        "vs_wired_pin": ratio_pin,
        "last_cells": [mp.nstr(v, 12) for v in tail5],
        "last_cell_ratios": ratios,
        "tail_strictly_decreasing_mp": dec,
    }
    guard("C2_%s_below_pin" % nm, float(mx) <= pin)
    guard("C2_%s_tail_decreasing" % nm, dec)

# ---------------------------------------------------------------------------
# D: mutation controls (in-memory, feasibility asserted)
# ---------------------------------------------------------------------------
# D1: a pin BELOW the certified render must fail the tie predicate
guard("D1_pin_control_feasible", not (fr(c4s) <= fr(60000000)))
# D2: wrong weight exponent must break the A3 spelling count (feasibility:
# the substitution really changes the string that A3 counts)
mut = src.replace("‖t / (2 * Real.pi)‖ ^ 4", "‖t / (2 * Real.pi)‖ ^ 3")
guard("D2_weight_control_feasible", mut.count("‖t / (2 * Real.pi)‖ ^ 4") == 0)

# ---------------------------------------------------------------------------
payload = {
    "record": 2722,
    "name": "2722C strip transport tie",
    "verdict": "STRIP-TRANSPORT-GREEN" if not failures else "STRIP-TRANSPORT-FAIL",
    "smoke": SMOKE,
    "wired_hypotheses_removed": 0,
    "premise_status": "three black-box strip premises replaced by two "
                       "identification equalities and three artifact-tied "
                       "pins on the explicit cardinal sum",
    "map103_freeze_unchanged": True,
    "producer_GO": False,
    "rh_claim": False,
    "pins": {"wiredQ": str(WQ), "wiredC4": WC4, "wiredC2": WC2},
    "numeric_tie": tie,
    "anchor_rel": checks.get("C1_anchor_rel"),
    "tail_extension": ext,
    "checks": checks,
    "failures": [list(f) for f in failures],
    "elapsed_s": round(time.time() - T_START, 2),
    "provenance": {
        "C1StripTransport2722C.lean": sha(LEAN),
        "C1ExplicitFiniteNodeCorrection.lean": sha(LEAN_1958),
        "C1FourPointRowBWired2721.lean": sha(LEAN_2721),
        "results/2720_p3_certified_strip_constants.json": sha(ART2720),
        "checker": sha(os.path.abspath(__file__)),
    },
}
if SMOKE:
    print("SMOKE: artifact not written")
else:
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(payload, fh, indent=2, default=str)
        fh.write("\n")
    print("wrote", OUT)
print("VERDICT:", payload["verdict"], "failures:", len(failures))
if failures:
    for f in failures:
        print("  -", f)
    sys.exit(1)
