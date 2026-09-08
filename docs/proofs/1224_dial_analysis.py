#!/usr/bin/env python3
"""Record 1224 sec.3a dial-sweep adjudication (MODEL, law 65).

Reproduces the 1213 extraction verbatim per dial JSON:
  - fine grade only (N=16384): Tn^cont = T_n * dt^2;
  - FP = intercept at Rn = 0 of the least-squares line through
    (Rn, Tn^cont) over the four ladder rungs, plus the 1213 per-rung
    "slope removed" variants;
  - ratio = FP / qw (qw read from the same JSON).

Registered gates (1224 sec.3a):
  - baseline replay (L10_S235) must match the committed 1213 FP_inf
    1.3791e33 within 2e-4 relative (regression gate on the edit);
  - qw bit-identical across the five dials (detector dial-invariance);
  - PINNED: all |dFP| < 1e-3; MOVES: any |dFP| >= 1e-3;
    ABORTED-UNINFORMATIVE: baseline regression fails or >= 2 dials have
    no complete 4-rung fine ladder.
Certifies nothing about the true owner; feeds only the 1224 Stage B
adjudication.  RH NOT claimed.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BASE_FP_1213 = 1.3791e33        # record 1213 headline FP_inf (fine)
FINE_N = 16384
DIALS = ["L10_S235", "L05_S235", "L20_S235", "L10_S2", "L10_S23571113"]


def fine_rows(d):
    rows = [r for r in d["results"] if r["N"] == FINE_N]
    return sorted(rows, key=lambda r: r["n"])


def fit_fp(rows):
    """Least-squares line through (Rn, Tn*dt^2); return (intercept, slope,
    n_used) and the per-rung 1213-style 'slope removed' readouts."""
    xs = [r["Rn"] for r in rows]
    ys = [r["Tn"] * r["dt"] ** 2 for r in rows]
    n = len(xs)
    if n < 4:
        return None
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx
    intercept = my - slope * mx
    per_rung = [y - slope * x for x, y in zip(xs, ys)]
    return dict(FP=intercept, slope=slope, n_used=n,
                spread_rel=(max(per_rung) - min(per_rung)) / abs(intercept),
                per_rung_FP=per_rung)


def main():
    out = {}
    for tag in DIALS:
        p = os.path.join(HERE, f"1224_dial_{tag}.json")
        if not os.path.exists(p):
            print(f"{tag:16s} MISSING (dial did not complete)")
            continue
        d = json.load(open(p))
        rows = fine_rows(d)
        fit = fit_fp(rows) if rows else None
        qw = d["qw"]["qw"]
        out[tag] = dict(qw=qw, lambda_=d["lambda_"], S=d["S"],
                        fit=fit)
        if fit is None:
            print(f"{tag:16s} NO-GO-S0-or-incomplete (fine rungs: "
                  f"{len(rows)})")
        else:
            print(f"{tag:16s} lambda={d['lambda_']:4.1f} S={d['S']}  "
                  f"FP={fit['FP']:+.6e}  FP/qw={fit['FP']/qw:+.6f}  "
                  f"slope={fit['slope']:+.3e}  rung spread={fit['spread_rel']:.1e}")

    if "L10_S235" not in out or out["L10_S235"]["fit"] is None:
        print("VERDICT: ABORTED-UNINFORMATIVE (baseline replay unavailable)")
        sys.exit(0)

    b = out["L10_S235"]["fit"]["FP"]
    reg = abs(b - BASE_FP_1213) / BASE_FP_1213
    print(f"\nbaseline replay vs 1213 FP_inf: rel diff {reg:.2e} "
          f"(gate 2e-4) -> {'PASS' if reg < 2e-4 else 'FAIL'}")
    qws = {t: o["qw"] for t, o in out.items()}
    same_qw = len(set(f"{v:.17e}" for v in qws.values())) == 1
    print(f"qw dial-invariance across completed dials: "
          f"{'PASS' if same_qw else 'FAIL ' + str(qws)}")

    if reg >= 2e-4 or not same_qw:
        print("VERDICT: ABORTED-UNINFORMATIVE (registered gate failed)")
        sys.exit(0)

    def rel(tag):
        o = out.get(tag)
        return None if not o or not o["fit"] else (o["fit"]["FP"] - b) / abs(b)

    dFP_lam_hi = rel("L20_S235")
    dFP_lam_lo = rel("L05_S235")
    dFP_lam = None if dFP_lam_hi is None or dFP_lam_lo is None \
        else dFP_lam_hi - dFP_lam_lo
    dFP_s_hi = rel("L10_S23571113")
    dFP_s_lo = rel("L10_S2")
    dFP_s = None if dFP_s_hi is None or dFP_s_lo is None \
        else dFP_s_hi - dFP_s_lo

    print(f"\ndFP(lambda) = {dFP_lam if dFP_lam is None else f'{dFP_lam:+.3e}'}  "
          f"(FP(2)-FP(0.5))/|FP(1)|")
    print(f"dFP(S)      = {dFP_s if dFP_s is None else f'{dFP_s:+.3e}'}  "
          f"(FP(S6)-FP(S1))/|FP(S3)|")
    for tag, r in rel_responses(out, b):
        print(f"  per-dial response {tag:16s}: {r:+.3e}")

    vals = [abs(v) for v in (dFP_lam, dFP_s) if v is not None]
    incomplete = sum(1 for t in DIALS if t not in out or out[t]["fit"] is None)
    if incomplete >= 2 or not vals:
        print("\nVERDICT: ABORTED-UNINFORMATIVE (>= 2 dials incomplete)")
    elif max(vals) >= 1e-3:
        print("\nVERDICT: MOVES — a dial-dependent term is present; the next "
              "addendum (before further runs) does the ledger-term "
              "identification of the FP response shape.")
    else:
        print("\nVERDICT: PINNED — the existing family's limit is dial-"
              "invariant at model level; the Cand-A value identity does not "
              "run through (lambda, S).")


def rel_responses(out, b):
    for tag in DIALS:
        o = out.get(tag)
        if o and o["fit"]:
            yield tag, (o["fit"]["FP"] - b) / abs(b)


if __name__ == "__main__":
    main()
