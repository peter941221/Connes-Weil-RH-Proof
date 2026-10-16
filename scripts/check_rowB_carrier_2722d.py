# -*- coding: utf-8 -*-
"""Record 2722D checker: row-B contradiction on the explicit cardinal carrier.

Sections
  A  transcription guards on C1RowBCardinalCarrier2722D.lean: the shifted
     CC20 triple literal, the vanishing/support theorem statements at the
     carrier term, the cardinal-sum pin quantifiers byte-verbatim from the
     record-2722C variant, the named-carrier def layout in hgate24/hprefix,
     and the verbatim refine call; A8 is the build-log census (skipped by
     --smoke, recorded visibly when absent);
  B  binder-diff of the new theorem against the parent
     fourPointContradictionRowBWired2722C: hvanish/hsupport/hbase/hcorr
     are GONE, the finite data conditions hsub/htri/hy are the only new
     binders, everything else carries over;
  C  mutation controls, feasibility-checked per the standing law: every
     rejection case re-evaluates the REAL guard on mutated text and the
     original passes that same guard immediately before;
  D  derivation tie: the shifted triple equals criticalVanishingPointValue
     values {0, 1/2, 1} shifted by 1/2, computed in exact Fractions from
     the committed CC20RHExit source;
  E  parent-file freeze: working bytes of the three consumed modules match
     their HEAD blobs (git hash-object).

Usage: python3 scripts/check_rowB_carrier_2722d.py [--smoke]
Writes results/2722d_rowB_carrier.json.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import time
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SMOKE = "--smoke" in sys.argv
T_START = time.time()

D2722 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                     "C1RowBCardinalCarrier2722D.lean")
A2722 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                     "C1RowBCardinalCarrier2722DAudit.lean")
PARENT = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                      "C1StripTransport2722C.lean")
W2721 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                     "C1FourPointRowBWired2721.lean")
CARRIER1958 = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                           "C1ExplicitFiniteNodeCorrection.lean")
EXIT_SRC_P = os.path.join(ROOT, "ConnesWeilRH", "Source", "CC20RHExit.lean")
BUILDLOG = os.path.join(ROOT, "_build_2722d.log")
OUT = os.path.join(ROOT, "results", "2722d_rowB_carrier.json")

failures = []
checks = {}


def sha256(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def md5(p):
    with open(p, "rb") as fh:
        return hashlib.md5(fh.read()).hexdigest()


def read(p):
    with open(p, encoding="utf-8") as fh:
        return fh.read()


def flat(s):
    return " ".join(s.split())


def record(name, ok, detail=""):
    checks[name] = {"pass": bool(ok), "detail": str(detail)}
    if not ok:
        failures.append(name)


def region(text, start_marker, end_marker):
    i = text.index(start_marker)
    j = text.index(end_marker, i)
    return text[i:j + len(end_marker)]


new_src = read(D2722)
new_flat = flat(new_src)
par_src = read(PARENT)

CARRIER_APP = "carrierSourceTest2722D targets nodes r hr y"
TRIPLE_LITERAL = "Finset ℂ := {(1 / 2 : ℂ), 1, (3 / 2 : ℂ)}"
DEF_BODY = ("def carrierSourceTest2722D (targets nodes : Finset ℂ) (r : ℝ)"
            " (hr : 0 < r) (y : ℂ → ℂ) : CompactLogTest :="
            " (selectedOwner (cardinalOwner targets (explicitSeed r hr)"
            " (fun _ => 1)) (cardinalOwner nodes (explicitSeed r hr) y)"
            " 3).sourceTest")
VANISH_STMT = ("CC20VanishesOn C1.healthyCC20TestSpace"
               " cc20TripleFiniteVanishingSet"
               " (selectedOwner (cardinalOwner targets (explicitSeed r hr)"
               " (fun _ => 1)) (cardinalOwner nodes (explicitSeed r hr) y)"
               " 3).sourceTest")
SUPPORT_STMT = ("Function.support (selectedOwner (cardinalOwner targets"
                " (explicitSeed r hr) (fun _ => 1)) (cardinalOwner nodes"
                " (explicitSeed r hr) y) 3).sourceTest.test ⊆"
                " Set.Ioo (-(5 * (2 * r + 1))) (5 * (2 * r + 1))")
PINS = {
    "A5_hcontractPin": (
        "(hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,"
        " 64 ≤ |t| → ‖cardinalSum targets (explicitSeed r hr)"
        " (fun _ => 1) ((sigma : Complex) + (t : Complex) * Complex.I)‖"
        " ≤ wiredQRowB2721)"),
    "A5_hquarticPin": (
        "(hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,"
        " ‖t / (2 * Real.pi)‖ ^ 4 * ‖cardinalSum targets"
        " (explicitSeed r hr) (fun _ => 1)"
        " ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ wiredC4RowB2721)"),
    "A5_hquadraticPin": (
        "(hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,"
        " ‖t / (2 * Real.pi)‖ ^ 2 * ‖cardinalSum nodes"
        " (explicitSeed r hr) y ((sigma : Complex) + (t : Complex) * Complex.I)‖"
        " ≤ wiredC2RowB2721)"),
    "A5_rho_caps": (
        "(hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)"
        " (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)"),
}
GATE_MARKS = ["ICgate", "24 ^ 2", "xiMultiplicity rho : Real",
              "spectralHeightShell k", "annihilatorDetectorSpanVector",
              "fullFunctionalEquationOrbitAnnihilator", "convolutionSquare",
              "involution.convolution"]
REFINE = ("refine fourPointContradictionRowBWired2722C targets nodes"
          " (explicitSeed r hr) (fun _ => 1) y"
          " (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))"
          " (cardinalOwner nodes (explicitSeed r hr) y) rho"
          " (B := 5 * (2 * r + 1)) hNorm hIm"
          " (carrier_cc20Vanishes2722D targets nodes hsub htri r hr y hy)"
          " (carrier_sourceTest_support2722D targets nodes r hr y)"
          " rfl rfl hcontractPin hquarticPin hquadraticPin hgate24 hprefix")
LABEL_RE = re.compile(r"\((h[A-Za-z0-9]+)\s*:")
LABEL_DENY = {"hr"}

main_thr = region(new_src, "theorem fourPointContradictionRowBCarrier2722D",
                  "False := by")
main_flat = flat(main_thr)
refine_flat = flat(new_src[new_src.index("False := by"):])
vthr_flat = flat(region(new_src, "theorem carrier_cc20Vanishes2722D", ":= by"))
sthr_flat = flat(region(new_src, "theorem carrier_sourceTest_support2722D",
                        ":= by"))

# ---------------------------------------------------------------- Section A
triple_flat = flat(region(new_src, "def shiftedCC20Triple2722D",
                          "{(1 / 2 : ℂ), 1, (3 / 2 : ℂ)}"))
record("A1_shifted_triple_literal",
       triple_flat == "def shiftedCC20Triple2722D : " + TRIPLE_LITERAL,
       triple_flat)
record("A2_vanish_statement", VANISH_STMT in vthr_flat, vthr_flat[:60])
record("A2_vanish_data_binders",
       "(htri : shiftedCC20Triple2722D ⊆ targets)" in vthr_flat and
       "(hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0)" in vthr_flat)
record("A3_support_statement", SUPPORT_STMT in sthr_flat)
record("A4_carrier_def_body", DEF_BODY in new_flat)
record("A4_carrier_def_single_declaration",
       new_src.count("def carrierSourceTest2722D") == 1)
for k, v in PINS.items():
    record(k, v in main_flat, v[:48])
record("A6_def_carrier_count8", main_flat.count(CARRIER_APP) == 8,
       "count=%d" % main_flat.count(CARRIER_APP))
UNFOLDED = ("(selectedOwner (cardinalOwner targets (explicitSeed r hr)"
            " (fun _ => 1)) (cardinalOwner nodes (explicitSeed r hr) y) 3)")
record("A6_main_theorem_uses_no_unfolded_carrier", UNFOLDED not in main_flat)
record("A6_gate_prefix_anchors", all(m in main_flat for m in GATE_MARKS))
record("A7_refine_verbatim", REFINE in refine_flat, REFINE[:60])
record("A7_conclusion_is_False", ": False := by" in main_flat)

census: "dict[str, object]" = {"log_present": os.path.exists(BUILDLOG)}
if SMOKE:
    census["note"] = "A8 skipped by --smoke"
elif not census["log_present"]:
    census["note"] = "build log absent; artifact records the gap visibly"
else:
    log = read(BUILDLOG)
    recs = re.findall(
        r"'(ConnesWeilRH[^']*?)' depends on axioms: \[([^\]]*)\]",
        re.sub(r",\s*\n\s*", ", ", log))
    census["records"] = len(recs)
    census["footer_ok"] = "Build completed successfully" in log
    census["error_lines"] = sum(1 for ln in log.splitlines()
                                if ln.startswith("error:"))
    census["sorry_lines"] = (log.count("sorryAx")
                             + log.count("declaration uses"))
    census["entry_path_warnings"] = sum(
        1 for ln in log.splitlines()
        if ln.startswith("warning:") and "2722D" in ln)
    expected_decls = {
        "ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.shiftedCC20Triple2722D",
        "ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.carrierSourceTest2722D",
        "ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.carrier_cc20Vanishes2722D",
        "ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.carrier_sourceTest_support2722D",
        "ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.fourPointContradictionRowBCarrier2722D",
    }
    got = {n for n, _ in recs}
    trios_ok = all(flat(t) == "propext, Classical.choice, Quot.sound"
                   for _, t in recs)
    record("A8_axiom_census",
           len(recs) == 5 and got == expected_decls and trios_ok and
           census["footer_ok"] and census["error_lines"] == 0 and
           census["sorry_lines"] == 0,
           "records=%d decls_ok=%s trio_ok=%s footer=%s err=%d sorry=%d"
           % (len(recs), got == expected_decls, trios_ok,
              census["footer_ok"], census["error_lines"],
              census["sorry_lines"]))
    record("A8_entry_warnings_zero", census["entry_path_warnings"] == 0,
           "n=%d" % census["entry_path_warnings"])
checks["A8_build_census"] = census

# ---------------------------------------------------------------- Section B
def labels_of(text):
    return sorted({m for m in LABEL_RE.findall(text) if m not in LABEL_DENY})


parent_thr = region(par_src, "theorem fourPointContradictionRowBWired2722C",
                    "False := by")
parent_labels = labels_of(parent_thr)
new_labels = labels_of(main_flat)
EXPECTED_PARENT = sorted(["hNorm", "hIm", "hvanish", "hsupport", "hbase",
                          "hcorr", "hcontractPin", "hquarticPin",
                          "hquadraticPin", "hgate24", "hprefix"])
EXPECTED_NEW = sorted(["hsub", "htri", "hy", "hNorm", "hIm", "hcontractPin",
                       "hquarticPin", "hquadraticPin", "hgate24", "hprefix"])
REMOVED = set(EXPECTED_PARENT) - set(EXPECTED_NEW)
ADDED = set(EXPECTED_NEW) - set(EXPECTED_PARENT)
record("B_parent_labels", parent_labels == EXPECTED_PARENT,
       ",".join(parent_labels))
record("B_new_labels", new_labels == EXPECTED_NEW, ",".join(new_labels))
record("B_removed_exactly4",
       set(parent_labels) - set(new_labels) == REMOVED,
       ",".join(sorted(set(parent_labels) - set(new_labels))))
record("B_added_exactly3", set(new_labels) - set(parent_labels) == ADDED,
       ",".join(sorted(set(new_labels) - set(parent_labels))))

# ---------------------------------------------------------------- Section C
# each control re-evaluates the real guard on mutated text; the unmutated
# original passes the same guard (asserted inline).
def control(name, original_ok, mutated_ok):
    record(name + "_original_passes", original_ok)
    record(name + "_mutation_rejected", (not mutated_ok) and original_ok,
           "guard must fail on the mutated text")


control("C1_pin_constant_swap",
        PINS["A5_hcontractPin"] in main_flat,
        PINS["A5_hcontractPin"] in
        main_flat.replace("wiredQRowB2721", "wiredC4RowB2721"))
control("C2_databinder_drop",
        labels_of(main_flat) == EXPECTED_NEW,
        labels_of(main_flat.replace("(htri : shiftedCC20Triple2722D",
                                   "(hXXX : shiftedCC20Triple2722D"))
        == EXPECTED_NEW)
control("C3_hvanish_reinsert",
        (set(parent_labels) - set(labels_of(main_flat))) == REMOVED,
        (set(parent_labels) -
         set(labels_of(main_flat + " (hvanish : True)"))) == REMOVED)
control("C4_B_term_perturb",
        REFINE in refine_flat,
        REFINE in refine_flat.replace("(B := 5 * (2 * r + 1))",
                                      "(B := 5 * (2 * r))"))
control("C5_triple_shift_wrong",
        TRIPLE_LITERAL in new_flat,
        TRIPLE_LITERAL in new_flat.replace("3 / 2 : ℂ)", "2 : ℂ)"))
control("C6_unnamed_carrier",
        main_flat.count(CARRIER_APP) == 8 and UNFOLDED not in main_flat,
        (main_flat.replace(CARRIER_APP, "X")).count(CARRIER_APP) == 8)

# ---------------------------------------------------------------- Section D
exit_src = read(EXIT_SRC_P)
D1_NEEDLE = ("cc20TripleFiniteVanishingSet : Finset CriticalVanishingPoint"
             " := {CriticalVanishingPoint.zero,"
             " CriticalVanishingPoint.half,"
             " CriticalVanishingPoint.one}")
record("D1_exit_triple_membership", D1_NEEDLE in flat(exit_src))
arms = re.findall(r"\| CriticalVanishingPoint\.(zero|half|one) => ([^|\n]+)",
                  exit_src)
vals = {}
for name, expr in arms:
    e = expr.strip().replace(" : ℂ", "").replace("(", "").replace(")", "")
    vals[name] = Fraction(e)
try:
    expected_shift = sorted(set(vals[k] + Fraction(1, 2) for k in vals))
except KeyError:
    expected_shift = []
lits = re.findall(r"\(([^)]*?) : ℂ\)", triple_flat) + ["1"]
parsed = sorted(set(Fraction(x.replace(" ", "")) for x in lits))
record("D2_shifted_triple_derivation",
       vals == {"zero": Fraction(0), "half": Fraction(1, 2),
               "one": Fraction(1)} and
       parsed == expected_shift == [Fraction(1, 2), Fraction(1),
                                    Fraction(3, 2)],
       "arms=%d shifted=%s parsed=%s" % (
           len(vals), [str(x) for x in expected_shift],
           [str(x) for x in parsed]))

# ---------------------------------------------------------------- Section E
blobs = {}
for p in (PARENT, W2721, CARRIER1958):
    rel = os.path.relpath(p, ROOT).replace("\\", "/")
    head = subprocess.check_output(
        ["git", "-C", ROOT, "rev-parse", "HEAD:" + rel]).decode().strip()
    live = subprocess.check_output(
        ["git", "-C", ROOT, "hash-object", p]).decode().strip()
    blobs[rel] = {"head_blob": head, "live_blob": live, "match": head == live}
record("E_parent_freeze_blob_match", all(v["match"] for v in blobs.values()),
       json.dumps({k: v["match"] for k, v in blobs.items()}))

# ---------------------------------------------------------------- output
n_checks = len([k for k in checks if k != "A8_build_census"])
elapsed = time.time() - T_START
payload = {
    "record": "2722D",
    "name": "rowB cardinal carrier instantiation",
    "date": "2026-10-17",
    "smoke": SMOKE,
    "verdict": ("CARRIER-INSTANTIATION-GREEN" if not failures
                else "CARRIER-INSTANTIATION-FAIL"),
    "transport_premises_proved": sorted(REMOVED),
    "rh_core_premises_still_named": ["hNorm", "hIm", "hcontractPin",
                                     "hquarticPin", "hquadraticPin",
                                     "hgate24", "hprefix"],
    "finite_data_conditions_added": sorted(ADDED),
    "wired_hypotheses_removed_this_round": sorted(REMOVED),
    "map103_freeze_unchanged": True,
    "producer_GO": False,
    "rh_claim": False,
    "carrier_growth_radius": "5 * (2 * r + 1)",
    "shifted_triple": ["1/2", "1", "3/2"],
    "binder_diff": {"parent": parent_labels, "new": new_labels},
    "build_census": census,
    "sources": {
        "C1RowBCardinalCarrier2722D.lean": {"md5": md5(D2722),
                                            "sha256": sha256(D2722)},
        "C1RowBCardinalCarrier2722DAudit.lean": {"md5": md5(A2722),
                                                 "sha256": sha256(A2722)},
    },
    "parent_blob_continuity": blobs,
    "checks": checks,
    "failures": failures,
    "checks_total": n_checks,
    "elapsed_s": round(elapsed, 2),
    "provenance": {"checker_sha256": sha256(__file__)},
}
os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(payload, fh, indent=2, sort_keys=True, ensure_ascii=False)
    fh.write("\n")

print("CHECKS: %d  FAILURES: %s" % (n_checks, failures or "NONE"))
print("verdict:", payload["verdict"])
print("elapsed: %.2f s" % elapsed)
sys.exit(0 if not failures else 1)
