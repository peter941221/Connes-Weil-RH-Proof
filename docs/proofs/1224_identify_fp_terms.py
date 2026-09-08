#!/usr/bin/env python3
"""Record 1224 sec.3b follow-through: closed-form ledger-term identification
of the FP dial response (MODEL, law 65; no eigsh ladder runs here).

The sweep (sec.3b, verdict MOVES) measured
  FP(L10_S2)=5.942349e32, FP(L10_S235)=1.379210e33,
  FP(L10_S23571113)=3.001164e33  (all at lambda=1).

Test (zero free parameters): if the S-dependence of FP is the arithmetic
carrier shape sum_{p in S} (log p / sqrt p) * Fhat_pm(log p) with UNIT
coefficient, where F is the model self-convolution g (*) conj-flip g as in
qw_terms, then

  [FP(S3)-FP(S1)] / [FP(S6)-FP(S3)]
    =? [sum_{p in {3,5}} w_p Fp] / [sum_{p in {7,11,13}} w_p Fp].

Second readout: with the same unit-coefficient hypothesis,
  A(lambda) := FP(lambda, S3) - sum_{p in {2,3,5}} w_p Fp
is the pure non-S part; report A at lambda = 0.5, 1, 2 (from sec.3b) and
test linearity in log(lambda) versus band-mass shape (registering that a
full 2x2 separation needs the follow-up dials (2,S1), (2,S6)).
"""
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
import importlib.util
spec = importlib.util.spec_from_file_location(
    "probe1212", __file__.replace("1224_identify_fp_terms.py",
                                  "1212_projection_trace_probe.py"))
p12 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p12)   # dials default (1.0 / 2,3,5); only pure
                               # model-g functions are used below

# --- measured FP values from record 1224 sec.3b --------------------------- #
FP = {("1.0", "S1"): 5.942349e32, ("1.0", "S3"): 1.379210e33,
      ("1.0", "S6"): 3.001164e33, ("0.5", "S3"): 1.622022e33,
      ("2.0", "S3"): 7.801646e32}
S3_PRIMES = [2, 3, 5]
S6_EXTRA = [7, 11, 13]


def carrier_values():
    """Fhat_pm(log p) on the model g, verbatim qw_terms machinery."""
    g, _ = p12.build_g_delta0()
    cvec = np.conj(g[(-np.arange(p12.NQ)) % p12.NQ])
    F = p12.circular_conv_centered(g, cvec)
    out = {}
    for p in S3_PRIMES + S6_EXTRA:
        lp = math.log(p)
        v = (float(np.interp(lp, p12.QS, F.real))
             + float(np.interp(-lp, p12.QS, F.real)))
        w = lp / math.sqrt(p)
        out[p] = dict(lp=lp, w=w, Fpm=v, wF=w * v)
    return out


def main():
    cv = carrier_values()
    print("model carrier readouts (MODEL g):")
    for p, d in sorted(cv.items()):
        print("  p=%2d  w=%.6f  F+-=%.6e  w*F=%.6e" %
              (p, d["w"], d["Fpm"], d["wF"]))

    s35 = sum(cv[p]["wF"] for p in (3, 5))
    s71113 = sum(cv[p]["wF"] for p in S6_EXTRA)
    pred = s35 / s71113
    meas = (FP[("1.0", "S3")] - FP[("1.0", "S1")]) / \
           (FP[("1.0", "S6")] - FP[("1.0", "S3")])
    print("\nunit-coefficient ratio test (zero free parameters):")
    print("  predicted [w3F3+w5F5]/[w7F7+w11F11+w13F13] = %+.6f" % pred)
    print("  measured  [FP(S3)-FP(S1)]/[FP(S6)-FP(S3)]   = %+.6f" % meas)
    rel = abs(pred - meas) / abs(pred)
    print("  relative mismatch = %.3e  -> %s" %
          (rel, "MATCH" if rel < 5e-2 else "MISMATCH"))

    # second readout: pure non-S part A(lambda) under unit coefficient
    s235 = sum(cv[p]["wF"] for p in S3_PRIMES)
    print("\nA(lambda) = FP(lambda,S3) - sum_{p in 2,3,5} w_p Fp:")
    a = {}
    for lam in ("0.5", "1.0", "2.0"):
        a[lam] = FP[(lam, "S3")] - s235
        print("  lambda=%s  A = %+.6e" % (lam, a[lam]))
    print("  A(1)-A(0.5) = %+.6e ;  A(2)-A(1) = %+.6e  "
          "(equal if linear in log lambda)" % (a["1.0"] - a["0.5"],
                                               a["2.0"] - a["1.0"]))
    print("\nRH NOT claimed; MODEL-labeled; registers the follow-up dials "
          "(lambda=2 x S1), (lambda=2 x S6) for full separation.")


if __name__ == "__main__":
    main()
