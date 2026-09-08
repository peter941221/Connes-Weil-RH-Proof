#!/usr/bin/env python3
"""Record 1224 sec.3d adjudication: lambda=2 S-row shape separation
(MODEL, law 65).  Reads the two new dial JSONs plus the committed
sec.3b L20_S235 / L10 row; same FP extraction as 1224_dial_analysis
(fit_fp / fine_rows imported verbatim).

Registered predictions (sec.3d, committed BEFORE the two runs):
  ADDITIVE       FP(2,S1) = -0.005e+33 ; FP(2,S6) = +2.402e+33
  MULTIPLICATIVE FP(2,S1) = +0.336e+33 ; FP(2,S6) = +1.698e+33

Adjudication rules (sec.3d):
  - sigma(dial) = per-rung FP spread (relative) * |FP(dial)| (floor 1e28);
  - a hypothesis is SUPPORTED if both new dials are within 3 sigma;
  - ADDITIVE xor MULTIPLICATIVE -> that verdict; neither -> MIXED, and a
    2-parameter solve FP(2,S) = k * (c + FP(1,S)) is reported (k = the
    implied alpha(2), c = the S-independent offset), with an anchor
    cross-check at S3;
  - any lambda=2-row rung spread > 2e-3 -> verdict CONDITIONAL
    (UNCONFIRMED fit quality), per the registered lambda=2 row rule;
  - a registered dial missing (or no fine ladder) -> ABORTED-UNINFORMATIVE;
  - anchor L20_S235 must replay within 2e-4 rel of the committed value.

Part (b) (registered): band-functional readout table — per dial, the
fine-grade means of pv_rank, pv_rel, pf_cond_hint, pv_cond_hint,
tail_gap — correlated with the FP row in the sec.3e addendum.

MODEL-labeled; certifies nothing about the true owner; RH NOT claimed.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import importlib.util

# digit-prefixed file name -> not importable by name; load by location
_spec = importlib.util.spec_from_file_location(
    "dial_analysis_1224", os.path.join(HERE, "1224_dial_analysis.py"))
assert _spec is not None and _spec.loader is not None
ana = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ana)   # fine_rows, fit_fp (main guarded)

# registered sec.3b measured FP values (committed data, docs/proofs)
B = {"S1": 5.942349e32, "S3": 1.379210e33, "S6": 3.001164e33,
     "L05_S3": 1.622022e33, "L20_S3": 7.801646e32}

SPREAD_FLAG = 2e-3      # sec.3d lambda=2 row fit-quality threshold
SIGMA_FLOOR = 1e28      # numeric-epsilon floor on sigma
MEAN_KEYS = ("pv_rank", "pv_rel", "pf_cond_hint", "pv_cond_hint",
             "tail_gap")


def read_dial(tag) -> "dict | None":
    """Return dict(fit=..., means={...}, qw=..., lam=..., S=...) or None
    when the JSON is absent.  fit is None when the fine ladder is absent."""
    p = os.path.join(HERE, f"1224_dial_{tag}.json")
    if not os.path.exists(p):
        return None
    with open(p) as fh:
        d = json.load(fh)
    rows = ana.fine_rows(d)
    fit = ana.fit_fp(rows) if rows else None
    means = {}
    for key in MEAN_KEYS:
        vals = [r[key] for r in rows if key in r]
        means[key] = sum(vals) / len(vals) if vals else float("nan")
    return dict(fit=fit, means=means, qw=d["qw"]["qw"],
                lam=d["lambda_"], S=d["S"])


def main():
    a1 = read_dial("L20_S2")             # new: lambda=2, S = {2}
    a6 = read_dial("L20_S23571113")      # new: lambda=2, S = {2,3,5,7,11,13}
    a3 = read_dial("L20_S235")           # committed sec.3b anchor of the row

    print("lambda=2 row (measured; sec.3b anchor from committed data):")
    for name, o in (("L20_S2", a1), ("L20_S235", a3),
                    ("L20_S23571113", a6)):
        if o is None:
            print("  %-16s MISSING" % name)
            continue
        fit = o["fit"]
        if fit is None:
            print("  %-16s NO fine ladder" % name)
            continue
        print("  %-16s FP=%+.6e  FP/qw=%+.6f  spread=%.1e  slope=%+.3e" %
              (name, fit["FP"], fit["FP"] / o["qw"],
               fit["spread_rel"], fit["slope"]))

    missing = [n for n, o in (("L20_S2", a1), ("L20_S235", a3),
                              ("L20_S23571113", a6)) if o is None]
    if missing:
        print("\nVERDICT: ABORTED-UNINFORMATIVE (missing: %s)" %
              ", ".join(missing))
        return
    assert a1 is not None and a3 is not None and a6 is not None
    fit1, fit3, fit6 = a1["fit"], a3["fit"], a6["fit"]
    incomplete = [n for n, f in (("L20_S2", fit1), ("L20_S235", fit3),
                                 ("L20_S23571113", fit6)) if f is None]
    if incomplete:
        print("\nVERDICT: ABORTED-UNINFORMATIVE (no fine ladder: %s)" %
              ", ".join(incomplete))
        return
    assert fit1 is not None and fit3 is not None and fit6 is not None

    # anchor replay gate (same code path as sec.3b)
    anchor_rel = abs(fit3["FP"] - B["L20_S3"]) / B["L20_S3"]
    print("\nanchor replay L20_S235 vs committed: rel diff %.2e (gate 2e-4) "
          "-> %s" % (anchor_rel, "PASS" if anchor_rel <= 2e-4 else "FAIL"))
    if anchor_rel > 2e-4:
        print("VERDICT: ABORTED-UNINFORMATIVE (anchor replay gate failed)")
        return

    y1 = fit1["FP"]
    y6 = fit6["FP"]
    sig1 = max(fit1["spread_rel"] * abs(y1), SIGMA_FLOOR)
    sig6 = max(fit6["spread_rel"] * abs(y6), SIGMA_FLOOR)

    pred_add = {"S1": B["L20_S3"] - (B["S3"] - B["S1"]),
                "S6": B["L20_S3"] + (B["S6"] - B["S3"])}
    pred_mul = {"S1": B["L20_S3"] * B["S1"] / B["S3"],
                "S6": B["L20_S3"] * B["S6"] / B["S3"]}

    print("\n3-sigma adjudication (sigma from per-dial rung spread):")
    for key, y, s in (("S1", y1, sig1), ("S6", y6, sig6)):
        print("  %s: measured %+.6e (sigma %.2e)" % (key, y, s))
        print("       ADD %+.6e  dev %+9.1f sigma" %
              (pred_add[key], (y - pred_add[key]) / s))
        print("       MUL %+.6e  dev %+9.1f sigma" %
              (pred_mul[key], (y - pred_mul[key]) / s))

    def supports(pred):
        return (abs(y1 - pred["S1"]) <= 3 * sig1 and
                abs(y6 - pred["S6"]) <= 3 * sig6)

    add_ok, mul_ok = supports(pred_add), supports(pred_mul)

    spread_flag = (fit1["spread_rel"] > SPREAD_FLAG or
                   fit3["spread_rel"] > SPREAD_FLAG or
                   fit6["spread_rel"] > SPREAD_FLAG)
    qual = ("  CONDITIONAL: row spread > %.0e -> UNCONFIRMED" % SPREAD_FLAG
            if spread_flag else "  (fit quality CLEAN)")

    if add_ok and not mul_ok:
        print("\nVERDICT: ADDITIVE" + qual)
    elif mul_ok and not add_ok:
        print("\nVERDICT: MULTIPLICATIVE" + qual)
    elif add_ok and mul_ok:
        print("\nVERDICT: DEGENERATE - both hypotheses within 3 sigma; "
              "registered separation (7-140 sigma) violated; re-inspect"
              + qual)
    else:
        # MIXED: FP(2,S) = k * (c + FP(1,S)); two equations, two unknowns.
        k = (y6 - y1) / (B["S6"] - B["S1"])
        c = y1 / k - B["S1"]
        print("\nVERDICT: MIXED" + qual)
        print("  2-parameter fit FP(2,S) = k*(c + FP(1,S)):")
        print("    k (implied alpha(2)) = %+.6e" % k)
        print("    c (S-independent)    = %+.6e  (%.3f * FP(1,S3))"
              % (c, c / B["S3"]))
        pred3 = k * (c + B["S3"])
        sig3 = max(fit3["spread_rel"] * abs(fit3["FP"]), SIGMA_FLOOR)
        print("  anchor check: fit predicts FP(2,S3) = %+.6e vs measured "
              "%+.6e (dev %+9.1f sigma)" %
              (pred3, fit3["FP"], (fit3["FP"] - pred3) / sig3))

    print("\npart (b) band-functional readout (fine-grade means):")
    print("  %-16s %10s %8s %12s %12s %12s" %
          ("dial", "pv_rank", "pv_rel", "pf_cond", "pv_cond", "tail_gap"))
    for tag in ("L10_S2", "L10_S235", "L10_S23571113", "L05_S235",
                "L20_S235", "L20_S2", "L20_S23571113"):
        o = read_dial(tag)
        if o is None or o["fit"] is None:
            print("  %-16s %10s" % (tag, "n/a"))
            continue
        m: dict = o["means"]
        print("  %-16s %10.0f %8.4f %12.4e %12.4e %12.4e" %
              (tag, m["pv_rank"], m["pv_rel"], m["pf_cond_hint"],
               m["pv_cond_hint"], m["tail_gap"]))

    print("\nMODEL-labeled; feeds only the 1224 Stage C decision.  "
          "RH NOT claimed.")


if __name__ == "__main__":
    main()
