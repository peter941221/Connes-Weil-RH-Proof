#!/usr/bin/env python3
"""Record 1224 sec.3f adjudication: the 3x3 FP grid and the parameter-free
row-volume rank test (MODEL, law 65).

Registered (sec.3f, committed before the runs):
  - new dials L05_S2, L05_S23571113 complete rows lambda=0.5;
  - replay gate: committed L05_S235 FP +1.622022e+33 within 2e-4;
  - falsification predictions for the two dead classes at the new points:
      ADDITIVE      FP(0.5,S1)=+0.837047e+33  FP(0.5,S6)=+3.243976e+33
      MULTIPLICATIVE FP(0.5,S1)=+0.698853e+33 FP(0.5,S6)=+3.529520e+33
  - primary statistic v = |det M| / (||row.5|| ||row1|| ||row2||) for the
    3x3 grid M (rows lambda = 0.5, 1, 2; columns S1, S3, S6), adjudicated
    against the registered linear upper bound dv = sum_i 3*maxcol_sigma_i
    / ||row_i||;
  - RANK-2 (v <= dv): report the global least-squares (c, k(0.5), k(2))
    alpha(lam)*(c + Phi(S)) fit over all nine points + per-point sigmas;
    RANK-3: report and hand to sec.3g (structure reading, no new runs);
  - positivity meta-check on all nine FP.

Extractor note (sec.3e fix): pv_rel lives in dense_validation and is a
dense-solve error diagnostic, not a band functional; reported here as a
sanity column only.

MODEL-labeled; certifies nothing about the true owner; RH NOT claimed.
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import importlib.util

_spec = importlib.util.spec_from_file_location(
    "dial_analysis_1224", os.path.join(HERE, "1224_dial_analysis.py"))
assert _spec is not None and _spec.loader is not None
ana = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ana)   # fine_rows, fit_fp (main guarded)

SIGMA_FLOOR = 1e28
LAMBDA_ORDER = [0.5, 1.0, 2.0]
S_ORDER = ["S1", "S3", "S6"]
TAGS = {
    (0.5, "S1"): "L05_S2", (0.5, "S3"): "L05_S235",
    (0.5, "S6"): "L05_S23571113",
    (1.0, "S1"): "L10_S2", (1.0, "S3"): "L10_S235",
    (1.0, "S6"): "L10_S23571113",
    (2.0, "S1"): "L20_S2", (2.0, "S3"): "L20_S235",
    (2.0, "S6"): "L20_S23571113",
}
# committed sec.3b/3d values for replay gates (relative 2e-4)
REPLAY = {"L05_S235": 1.622022e33, "L20_S235": 7.801646e32,
          "L10_S235": 1.379210e33}


def read_fp(tag):
    """Return (FP, sigma, dense_pv_rel) or (None, None, None)."""
    p = os.path.join(HERE, f"1224_dial_{tag}.json")
    if not os.path.exists(p):
        return None, None, None
    with open(p) as fh:
        d = json.load(fh)
    rows = ana.fine_rows(d)
    fit = ana.fit_fp(rows) if rows else None
    if fit is None:
        return None, None, None
    sigma = max(fit["spread_rel"] * abs(fit["FP"]), SIGMA_FLOOR)
    return fit["FP"], sigma, d.get("dense_validation", {}).get("pv_rel")


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def norm(v):
    return math.sqrt(sum(x * x for x in v))


def main():
    fp, sig, pvrel, missing = {}, {}, {}, []
    for key, tag in TAGS.items():
        v, s, pr = read_fp(tag)
        if v is None:
            missing.append(tag)
        fp[key], sig[key], pvrel[key] = v, s, pr

    print("3x3 FP grid (e+32):")
    for lam in LAMBDA_ORDER:
        cells = []
        for s in S_ORDER:
            v = fp[(lam, s)]
            cells.append("   MISSING" if v is None else "%10.4f" % (v / 1e32))
        print("  lambda=%3.1f  %s" % (lam, "  ".join(cells)))

    if missing:
        print("\nVERDICT: ABORTED-UNINFORMATIVE (missing: %s)" %
              ", ".join(missing))
        return

    # replay gates on the three committed anchor dials
    ok = True
    for tag, committed in REPLAY.items():
        key = next(k for k, t in TAGS.items() if t == tag)
        rel = abs(fp[key] - committed) / committed
        state = "PASS" if rel <= 2e-4 else "FAIL"
        print("replay %s: rel %.2e (gate 2e-4) -> %s" % (tag, rel, state))
        ok = ok and rel <= 2e-4
    if not ok:
        print("VERDICT: ABORTED-UNINFORMATIVE (replay gate failed)")
        return

    # positivity meta-check
    neg = [k for k in fp if fp[k] <= 0]
    print("positivity meta-check: %s" % ("ALL 9 FP > 0" if not neg else
                                         "RED FLAG negatives: %s" % neg))

    # falsification predictions for the dead classes
    B = {"S1": fp[(1.0, "S1")], "S3": fp[(1.0, "S3")], "S6": fp[(1.0, "S6")],
         "L05_S3": fp[(0.5, "S3")], "L20_S3": fp[(2.0, "S3")]}
    pred_add = {"S1": B["L05_S3"] + (B["S1"] - B["S3"]),
                "S6": B["L05_S3"] + (B["S6"] - B["S3"])}
    pred_mul = {"S1": B["L05_S3"] * B["S1"] / B["S3"],
                "S6": B["L05_S3"] * B["S6"] / B["S3"]}
    print("\nsec.3f falsification readout (new points):")
    for s in ("S1", "S6"):
        y = fp[(0.5, s)]
        sg = sig[(0.5, s)]
        print("  %s: measured %+.6e (sigma %.2e)" % (s, y, sg))
        print("       ADD %+.6e  dev %+9.1f sigma" %
              (pred_add[s], (y - pred_add[s]) / sg))
        print("       MUL %+.6e  dev %+9.1f sigma" %
              (pred_mul[s], (y - pred_mul[s]) / sg))

    # primary registered statistic: normalized row volume
    rows = [[fp[(lam, s)] for s in S_ORDER] for lam in LAMBDA_ORDER]
    nrm = [norm(r) for r in rows]
    v = abs(det3(rows)) / (nrm[0] * nrm[1] * nrm[2])
    dv = 0.0
    for i, lam in enumerate(LAMBDA_ORDER):
        smax = max(sig[(lam, s)] for s in S_ORDER)
        dv += 3.0 * smax / nrm[i]
    print("\nrow-volume statistic:  v = %.3e   dv(3-sigma bound) = %.3e  "
          "-> %s" % (v, dv, "RANK-2 (v <= dv)" if v <= dv else
                     "RANK-3 (v > dv)"))

    # companion diagnostic (no new runs): shifted-row determinants of the
    # full alpha(lam)*(c+Phi(S)) class, i.e. rank{r_lam, r_1, e} <= 2 tests
    for lam in (0.5, 2.0):
        r = [fp[(lam, s)] for s in S_ORDER]
        r1v = rows[1]
        e = [1.0, 1.0, 1.0]
        d2 = abs(det3([r, r1v, e])) / (norm(r) * nrm[1] * norm(e))
        print("  class check: vol(r_%s, r_1, ones) = %.3e" % (lam, d2))

    if v <= dv:
        # global least-squares of FP(lam,S) = a(lam) + b(lam)*Phi(S) is the
        # same class; per the registered sec.3f text report (c, k(.5), k(2))
        # fit of alpha(lam)*(c + Phi(S)) with normalization k(1)=1:
        # FP(lam,S) = k(lam)*(FP(1,S) - c*0 + ... ) -> do the honest 2-param
        # per-row solve with the lambda=1 row taken as reference:
        # FP(lam,S) = k*(FP(1,S) + shift).  Solve (k, shift) per lam.
        print("\nRANK-2: per-row affine fits FP(lam,S) = k*(FP(1,S)+shift):")
        for lam in (0.5, 2.0):
            x = rows[1]
            y = [fp[(lam, s)] for s in S_ORDER]
            w = [1.0 / sig[(lam, s)] ** 2 for s in S_ORDER]
            sw = sum(w)
            sx = sum(wi * xi for wi, xi in zip(w, x)) / sw
            sy = sum(wi * yi for wi, yi in zip(w, y)) / sw
            sxx = sum(wi * xi * xi for wi, xi in zip(w, x)) / sw
            sxy = sum(wi * xi * yi for wi, xi, yi in zip(w, x, y)) / sw
            k = (sxy - sx * sy) / (sxx - sx * sx)
            shift = sy / k - sx
            resid = []
            for s, xi, yi in zip(S_ORDER, x, y):
                r_ = yi - k * (xi + shift)
                resid.append("%s %+7.1f sig" % (s, r_ / sig[(lam, s)]))
            print("  lam=%.1f: k=%+.6f  shift=%+.6e (%+.3f*FP(1,S3))  "
                  "residuals %s" % (lam, k, shift, shift / B["S3"],
                                    "  ".join(resid)))
    else:
        print("\nRANK-3: the 3x3 grid is full-rank; no separable or "
              "2-parameter counterterm class can match the FP surface.  "
              "Structure reading proceeds in sec.3g (committed data only).")

    print("\nsanity (dense_validation.pv_rel, target < 1e-9): " +
          "  ".join("%s=%.1e" % (TAGS[k], pvrel[k])
                    for k in sorted(TAGS) if pvrel[k]))
    print("MODEL-labeled; feeds only the 1224 Stage C decision.  "
          "RH NOT claimed.")


if __name__ == "__main__":
    main()
