#!/usr/bin/env python3
"""Record 2722E: stored row-B witness data-leg screen.

Binding-route contract (core-progress gate form per the project route
rules in docs/map):

  consumer  : the ten hypotheses of fourPointContradictionRowBCarrier2722D
              (record 2722D) at a concrete carrier;
  owner     : the stored row-B lane configuration (record 1980 builder at
              gamma_2 = 21.022039638771556, re = 0.55, N = 5: 8 healthy
              targets, 56-node owner, stored correction values);
  question  : does the stored configuration satisfy the data-side legs
              hsub / htri / hy (finite data), hNorm / hIm (wired rho caps)
              and the three cardinal-sum pins (artifact-grade envelope)
              WITHOUT any node-set enlargement -- the 2722D residual (1)
              asked whether a reopen witness must "include the shifted
              triple in its targets with y = 0 there" and re-price the
              pins for the enlarged list;
  decision  : the record-1980 healthy_targets list ALREADY contains the
              shifted triple {1/2, 1, 3/2} exactly (binary64-exact values)
              and the stored correction values vanish there exactly, so
              this screen verifies the stored class leg-by-leg in exact
              arithmetic and re-prices the pins for the stored lists in
              the same run, bitwise-anchored against the committed
              record-2720 and record-2722C artifacts;
  completion: every section guard GREEN with explicit margins, anchors
              rel == 0.0 against the committed renders, mutation controls
              feasible (the original passes first, the perturbation
              fails);
  budget    : one script, one artifact, no Lean build, no enlargement
              enumeration (same-run reprice law, record 2057);
  stop      : at the verdict.  hgate24 / hprefix (the RH core) are NOT
              touched; a screen pass is model-grade/artifact-grade
              support, never a producer GO.

Sections
  E1  exact finite-data screen (binary64 -> Fraction): triple subset of
      targets, targets subset of owner, stored y == 0 exactly on the
      triple, base y == 1 exactly, plus configuration-cardinality anchors
      against the committed 2720 row B;
  E2  wired rho caps hNorm / hIm in exact arithmetic (caps 22 and 421/20
      parsed from C1FourPointRowBWired2721.lean);
  E3  pin reprice on the stored lists: same p3 engine, same run; bitwise
      anchors against the committed 2720 artifact (rel 0.0), margins
      against the wired pins equal to the committed 2722C tie;
  E4  tail extension [600, 1e7] both signs, three channels, bitwise
      anchors against the committed 2722C artifact, below-pin guards and
      mp-native strict-decrease evidence;
  E5  feasibility-checked mutation controls (drop a triple point, flip a
      stored y, raise Im past the cap, lower the C4 pin under the star).

Writes results/2722e_witness_data_screen.json.
Usage: python3 scripts/witness_data_screen_2722e.py
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
T_START = time.time()

P3 = os.path.join(ROOT, "scripts", "p3_certified_strip_constants_2720.py")
ART2720 = os.path.join(ROOT, "results", "2720_p3_certified_strip_constants.json")
ART2722C = os.path.join(ROOT, "results", "2722c_strip_transport_tie.json")
WIRE = os.path.join(ROOT, "ConnesWeilRH", "Dev", "C1FourPointRowBWired2721.lean")
OUT = os.path.join(ROOT, "results", "2722e_witness_data_screen.json")

# wired pins (must match the Lean defs verbatim; same literals as 2722C)
WQ = Fraction(26, 10 ** 17)
WC4 = Fraction(61000000)
WC2 = Fraction(29000000)

failures = []
checks = {}


def sha(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def guard(name, ok, detail=""):
    checks[name] = bool(ok)
    if not ok:
        failures.append((name, detail))
    print(("PASS " if ok else "FAIL ") + name + (" " + detail if detail else ""))


def fr(x):
    return Fraction(x)


def frc(c):
    """Exact (re, im) Fraction pair of a stored binary64 complex."""
    return (Fraction(c.real), Fraction(c.imag))


# ---------------------------------------------------------------------------
# E0: load the committed engine (record-2722C pattern) and the row-B list
# ---------------------------------------------------------------------------
spec = importlib.util.spec_from_file_location("p3_2720", P3)
assert spec is not None and spec.loader is not None, "p3_2720 loader unavailable"
p3 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p3)

row = p3.Row_(p3.CANDIDATES[1])
art = json.load(open(ART2720, encoding="utf-8"))
artc = json.load(open(ART2722C, encoding="utf-8"))
rowB = art["rows"][1]
assert rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5
cert = rowB["certified"]

TRIPLE = [(Fraction(1, 2), Fraction(0)),
          (Fraction(1), Fraction(0)),
          (Fraction(3, 2), Fraction(0))]

# ---------------------------------------------------------------------------
# E1: exact finite-data screen
# ---------------------------------------------------------------------------
targets_f = [frc(z) for z in row.targets]
owner_f = [frc(z) for z in row.owner]

for i, t in enumerate(TRIPLE):
    _ok = t in targets_f
    guard("E1.triple_in_targets[%d]" % i, _ok,
          "" if _ok else "shifted node %s absent from the stored targets"
          % (t,))
guard("E1.targets_subset_owner",
      all(t in owner_f for t in targets_f))
triple_owner_idx = [k for k, z in enumerate(owner_f) if z in TRIPLE]
guard("E1.triple_owner_count", len(triple_owner_idx) == 3,
      "indices %s" % triple_owner_idx)
guard("E1.hy_stored_y_zero_on_triple",
      all(row.values[k] == 0j for k in triple_owner_idx))
guard("E1.base_y_one_everywhere",
      all(v == complex(1.0, 0.0) for v in row.base_values))
guard("E1.targets_distinct", len(set(targets_f)) == len(targets_f))
guard("E1.owner_distinct", len(set(owner_f)) == len(owner_f))
# structural anchors against the committed 2720 row (lists feed the engine)
guard("E1.cardinalities_match_2720",
      len(row.owner) == rowB["owner_cardinality"]
      and len(row.targets) == 8 and row.corr_nodes is not None,
      "owner %d targets %d" % (len(row.owner), len(row.targets)))
guard("E1.corr_active_match_2720",
      len([v for v in row.values if abs(v) > 0.5]) == rowB["corr_active"])
# the shifted triple is EXACTLY the 1980 healthy-target tail nodes: the
# witness was built with the vanishing triple; binary64 0.5/1.0/1.5 equal
# the rationals 1/2, 1, 3/2 with zero conversion error.
guard("E1.triple_binary64_exact",
      frc(complex(0.5, 0.0)) == TRIPLE[0]
      and frc(complex(1.0, 0.0)) == TRIPLE[1]
      and frc(complex(1.5, 0.0)) == TRIPLE[2])

# ---------------------------------------------------------------------------
# E2: wired rho caps (parse the literals from the pinned 2721 module)
# ---------------------------------------------------------------------------
wsrc = open(WIRE, encoding="utf-8").read()
# multi-token capture law (record 2722C): a spaced literal like "421 / 20"
# is never equal to a \S+ run; take the whole line to the newline.
m_norm = re.search(r"def wiredRhoNormCapRowB2721 : Real := ([^\n]+)", wsrc)
m_im = re.search(r"def wiredRhoImCapRowB2721 : Real := ([^\n]+)", wsrc)
assert m_norm is not None and m_im is not None, "rho cap defs not found"
cap_norm_s = m_norm.group(1).strip()
cap_im_s = m_im.group(1).strip()
assert cap_norm_s == "22" and cap_im_s == "421 / 20", "cap spelling drift"
cap_norm = Fraction(22)
cap_im = Fraction(421, 20)
rho_f = frc(row.rho)
norm2 = rho_f[0] ** 2 + rho_f[1] ** 2
guard("E2.hNorm", norm2 <= cap_norm ** 2,
      "norm^2=%.6f cap^2=%d" % (float(norm2), cap_norm ** 2))
guard("E2.hNorm_margin", cap_norm ** 2 - norm2,
      "squared-cap margin %.6f" % float(cap_norm ** 2 - norm2))
guard("E2.hIm", abs(rho_f[1]) <= cap_im,
      "|im| = %s, cap = 421/20, margin = %s"
      % (rho_f[1], cap_im - abs(rho_f[1])))

# ---------------------------------------------------------------------------
# E3: pin reprice on the stored lists (same engine, same run, bitwise anchor)
# ---------------------------------------------------------------------------
D, ctl = p3.certified_D_table()
guard("E3.D_table_controls", ctl[1] and ctl[2])
cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)
sup_b, C4rep = p3.scan_channel(cb, 4, D)
sup_c, C2rep = p3.scan_channel(cc, 2, D)
q64rep = p3.q_star_at(cb, 64, D)
rel = lambda a, b: abs(a - b) / max(abs(b), 1e-300)
checks["E3.anchor_rel"] = {"C4": rel(C4rep, cert["C4_star"]),
                           "C2": rel(C2rep, cert["C2_star_corr"]),
                           "q": rel(q64rep, cert["q_star_T64"])}
guard("E3.anchor_C4_bitwise", rel(C4rep, cert["C4_star"]) == 0.0)
guard("E3.anchor_C2_bitwise", rel(C2rep, cert["C2_star_corr"]) == 0.0)
guard("E3.anchor_q_bitwise", rel(q64rep, cert["q_star_T64"]) == 0.0)
tie = {"C4_star": C4rep, "C4_pin": float(WC4), "C4_margin": float(WC4) - C4rep,
       "C2_star": C2rep, "C2_pin": float(WC2), "C2_margin": float(WC2) - C2rep,
       "q_star_T64": q64rep, "q_pin": float(WQ),
       "q_margin": float(WQ - fr(q64rep))}
guard("E3.tie_equals_2722C",
      all(tie[k] == artc["numeric_tie"][k] for k in tie),
      "same-run tie must equal the committed 2722C renders")
guard("E3.pin_q", fr(q64rep) <= WQ)
guard("E3.pin_C4", fr(C4rep) <= WC4)
guard("E3.pin_C2", fr(C2rep) <= WC2)
guard("E3.q_positive", fr(q64rep) > 0)
margins = {"C4_frac_of_pin": float(WC4 - fr(C4rep)) / float(WC4),
           "C2_frac_of_pin": float(WC2 - fr(C2rep)) / float(WC2),
           "q_frac_of_pin": float(WQ - fr(q64rep)) / float(WQ)}
checks["E3.margins_frac_of_pin"] = margins

# ---------------------------------------------------------------------------
# E4: tail extension [TAIL_T, 1e7], both signs (record-2722C machinery)
# ---------------------------------------------------------------------------
T0 = float(p3.TAIL_T)
TMAX = 1.0e7


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
for nm, consts, wp, pin, key in [
    ("base_quartic", cb, 4, WC4, "base_quartic"),
    ("corr_quadratic", cc, 2, WC2, "corr_quadratic"),
    ("base_contract", cb, 0, WQ, "base_contract"),
]:
    mx, vals = extend(consts, wp)
    committed = artc["tail_extension"][key]["max_weighted_envelope"]
    checks["E4.anchor_rel_%s" % nm] = rel(float(mx), committed)
    guard("E4.anchor_%s" % nm, rel(float(mx), committed) <= 1e-12)
    tail5 = vals[-6:]
    dec = all(tail5[i + 1] < tail5[i] for i in range(len(tail5) - 1))
    ratios = [float(tail5[i + 1] / tail5[i]) for i in range(len(tail5) - 1)]
    assert all(r > 0 for r in ratios), "mp ratio display underflow"
    ext[nm] = {"range": [T0, TMAX], "cells": len(vals),
               "max_weighted_envelope": float(mx),
               "vs_wired_pin": float(mx) / float(pin),
               "last_cells": [mp.nstr(v, 12) for v in tail5],
               "last_cell_ratios": ratios,
               "tail_strictly_decreasing_mp": dec}
    guard("E4.%s_below_pin" % nm, float(mx) <= float(pin))
    guard("E4.%s_tail_decreasing" % nm, dec)

# ---------------------------------------------------------------------------
# E5: feasibility-checked mutation controls
# ---------------------------------------------------------------------------
# m1: drop the middle triple point from a targets COPY -> membership fails;
# feasibility: the untouched list passes the same predicate first.
mut_targets = [t for t in targets_f if t != TRIPLE[1]]
guard("E5.m1_feasible_drop_triple",
      TRIPLE[1] in targets_f and TRIPLE[1] not in mut_targets)
# m2: flip the stored y at the first triple owner index -> hy fails.
mut_values = list(row.values)
mut_values[triple_owner_idx[0]] = complex(1.0, 0.0)
guard("E5.m2_feasible_flip_y",
      all(row.values[k] == 0j for k in triple_owner_idx)
      and not all(mut_values[k] == 0j for k in triple_owner_idx))
# m3: rho with Im past the cap -> hIm predicate fails (cap 21.05).
mut_im = Fraction(2106, 100)
guard("E5.m3_feasible_raise_im",
      abs(rho_f[1]) <= cap_im and not mut_im <= cap_im)
# m4: a C4 pin BELOW the certified star must fail the tie predicate
# (feasibility: the wired pin passes first; same form as 2722C D1).
guard("E5.m4_feasible_lower_pin",
      fr(C4rep) <= WC4 and not (fr(C4rep) <= Fraction(60000000)))

# ---------------------------------------------------------------------------
# verdict + artifact
# ---------------------------------------------------------------------------
if failures:
    verdict = "WITNESS-SCREEN-CONTROL-FAIL"
elif (all(checks[k] for k in checks if isinstance(checks[k], bool))):
    verdict = "STORED-WITNESS-DATA-LEG-GREEN"
else:
    verdict = "WITNESS-SCREEN-CONTROL-FAIL"

payload = {
    "record": 2722,
    "name": "2722E stored row-B witness data-leg screen",
    "verdict": verdict,
    "lane": "map-103 reopen motion, premise-shrink lane (2721B/C, "
            "2722A/B/C/D): decides the witness-data question left open by "
            "the 2722D residual (1)",
    "decision": "the stored row-B configuration satisfies every data-side "
                "leg of fourPointContradictionRowBCarrier2722D: the shifted "
                "CC20 triple {1/2, 1, 3/2} is contained in the record-1980 "
                "healthy targets EXACTLY (binary64-exact values), the "
                "stored correction values vanish there EXACTLY, targets "
                "sit inside the owner list, the stored rho respects both "
                "wired caps, and the three cardinal-sum pins hold at "
                "artifact-grade with margins re-priced bitwise the same "
                "2722C tie. No node-set enlargement is required for the "
                "finite-data legs; any future gate-index enlargement must "
                "re-earn the thin pin headroom reported here.",
    "pin_margins_frac_of_pin": margins,
    "numeric_tie": tie,
    "anchor_rel_E3": checks["E3.anchor_rel"],
    "tail_extension": ext,
    "wired_pins": {"wiredQ": str(WQ), "wiredC4": str(WC4),
                   "wiredC2": str(WC2), "rhoNormCap": str(cap_norm),
                   "rhoImCap": str(cap_im)},
    "configuration": {"gamma": row.cand["gamma"], "N": row.cand["N"],
                      "rho": [float(row.rho.real), float(row.rho.imag)],
                      "targets": [[float(z.real), float(z.imag)]
                                  for z in row.targets],
                      "owner_cardinality": len(row.owner),
                      "corr_active": len([v for v in row.values
                                          if abs(v) > 0.5]),
                      "triple_owner_indices": triple_owner_idx},
    "wired_hypotheses_removed": 0,
    "residuals_named": [
        "hgate24: P5 gate sign on the carrier source test (RH core, "
        "map-103 frozen premise -- untouched by this screen)",
        "hprefix: P2 six-shell prefix bound (RH core, frozen)",
        "Lean-grade discharge of the three cardinal pins (2720 D-ladder + "
        "interval-cell envelope inside Lean; 2722D residual (2))",
        "model-to-Lean transfer: exact-rational capture of the stored "
        "8-target / 56-owner lists and values, explicitSeed identification "
        "for the model seed, and the node-radius owner transfer brick "
        "(2720 nonclaims)",
    ],
    "map103_freeze_unchanged": True,
    "producer_GO": False,
    "rh_claim": False,
    "checks": checks,
    "failures": [list(f) for f in failures],
    "elapsed_s": round(time.time() - T_START, 2),
    "provenance": {
        "scripts/p3_certified_strip_constants_2720.py": sha(P3),
        "results/2720_p3_certified_strip_constants.json": sha(ART2720),
        "results/2722c_strip_transport_tie.json": sha(ART2722C),
        "C1FourPointRowBWired2721.lean": sha(WIRE),
        "checker": sha(os.path.abspath(__file__)),
    },
}
with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(payload, fh, indent=2, default=str)
    fh.write("\n")
print("wrote", os.path.basename(OUT))
print("VERDICT:", payload["verdict"], "failures:", len(failures))
if failures:
    for f in failures:
        print("  -", f)
    sys.exit(1)
