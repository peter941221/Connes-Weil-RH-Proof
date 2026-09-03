"""1107 - SOS upper-bound machinery diagnostic preview.
Ingredients: lambda_min(Z_N|_V) vs measured tail mass tau_N, per
docs/proofs/1107_sos_upper_bound_preregistration.md. Verbatim p6_weil
zero_gram construction from the 1105 bundle; diagnostic float64; no
certified bound; RH not claimed."""
import os
import sys

import numpy as np
from scipy.linalg import eigh

BUNDLE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "1105_weil_identity_bundle")
sys.path.insert(0, BUNDLE)
import f0
import p6_weil

F1_ANCHORS = {
    (2.0, 8): dict(top_arch=0.854466, min_prime=-0.858729,
                    top_arch_minus_prime=1.712992),
    (4.0, 8): dict(top_arch=1.781109, min_prime=-1.781212,
                    top_arch_minus_prime=3.562321),
}


def symev(m):
    return eigh((m + m.T) / 2.0, eigvals_only=True)


def main():
    print("1107 SOS upper-bound diagnostic preview "
          "(pre-reg: 1107_sos_upper_bound_preregistration.md)")
    print(f"python={sys.version.split()[0]} numpy={np.__version__}")

    worst = 0.0
    for (a, K), ref in F1_ANCHORS.items():
        r = f0.tops(a, K)
        for key, val in ref.items():
            worst = max(worst, abs(r[key] - val))
    print(f"f0 anchor drift = {worst:.2e} (abort > 2e-3)")
    if worst > 2e-3:
        print("VERDICT: ABORT-ANCHOR")
        return

    best = -1.0
    best_at = None
    for a, K in [(2.0, 8), (4.0, 8)]:
        ref = p6_weil.zero_gram(a, K, Nz=600, tail=True)
        Z_ref = ref["Z"]
        topM = float(symev(ref["M"])[-1])
        print(f"\ncell (a={a:g}, K={K}): top(M) = {topM:+.3e}  "
              f"(orientation; identity residual discussion in pre-reg s1)")
        for N in (60, 120, 300):
            r = p6_weil.zero_gram(a, K, Nz=N, tail=False)
            Z_N = r["Z"]
            lam = float(symev(Z_N)[0])
            tau = float(np.linalg.norm(Z_ref - Z_N))
            m = lam - tau
            ok = m > 1e-7
            if m > best:
                best, best_at = m, (a, K, N)
            print(f"  N={N:<4d} lam_min(Z_N)={lam:+.3e}  tau_N={tau:.3e}  "
                  f"margin m_N={m:+.3e}  {'PASS' if ok else 'fail'}")
    verdict = best > 1e-7
    print(f"\nbest preview margin = {best:+.3e} at {best_at} "
          f"(criterion > 1e-7)")
    print(f"VERDICT: {'PASS' if verdict else 'FAIL'}")
    print("DONE")


if __name__ == "__main__":
    main()
