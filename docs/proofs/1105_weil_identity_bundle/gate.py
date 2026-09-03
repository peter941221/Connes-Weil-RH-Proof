"""1105 gate layer (the ONLY in-house code): evaluates the pre-registered
gates G-A..G-D against the VERBATIM external runners f0/p6_weil/f3_random
(docs/proofs/1105_weil_identity_verification_preregistration.md).
Diagnostic float64; RH not claimed.
"""
import math
import os
import sys

import numpy as np
from scipy.linalg import eigh

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import f0
import p6_weil
import f3_random

GAM1 = 14.1347251417469

# committed F.1 anchors (this repo's prompt-006 round-3 F.1 block)
F1_ANCHORS = {
    (2.0, 8): dict(top_arch=0.854466, min_prime=-0.858729,
                    top_arch_minus_prime=1.712992),
    (4.0, 8): dict(top_arch=1.781109, min_prime=-1.781212,
                    top_arch_minus_prime=3.562321),
}

# external-reported P-2 reference values (a=4, K=8, seeds 1..5)
P2_REF = {
    "2a-perm": [1.546, 1.099, 1.568, 1.447, 1.260],
    "2b-unif": [1.751, 3.254, 0.953, 0.982, 8.273],
    "2c-rndw": [1.767, 1.860, 1.519, 1.505, 2.092],
}


def symev(m):
    return eigh((m + m.T) / 2.0, eigvals_only=True)


def main():
    print("1105 gate layer (pre-reg: 1105_weil_identity_verification_preregistration.md)")
    print(f"python={sys.version.split()[0]} numpy={np.__version__}")

    # ---- f0 anchor sanity (ABORT gate) -----------------------------------
    worst_anchor = 0.0
    for (a, K), ref in F1_ANCHORS.items():
        r = f0.tops(a, K)
        for key, val in ref.items():
            worst_anchor = max(worst_anchor, abs(r[key] - val))
    print(f"f0 anchor drift vs committed F.1 = {worst_anchor:.2e} (abort > 2e-3)")
    if worst_anchor > 2e-3:
        print("VERDICT: ABORT-ANCHOR")
        return

    # ---- G-A / G-B: identity + pin depth via THEIR zero_gram -------------
    ga = True
    gb = True
    tail_note = []
    for a, K in [(2.0, 8), (4.0, 8), (2.0, 16)]:
        r = p6_weil.zero_gram(a, K)
        M, Z, A, Zd = r["M"], r["Z"], r["A"], r["Z_discrete"]
        nA = np.linalg.norm(A)
        kap = float(np.sum(M * Z) / np.sum(Z * Z))
        resid = float(np.linalg.norm(M - kap * Z) / nA)
        kap_d = float(np.sum(M * Zd) / np.sum(Zd * Zd))
        resid_d = float(np.linalg.norm(M - kap_d * Zd) / nA)
        evM, evZ = symev(M), symev(Z)
        ok_A = resid <= 1e-4 and (-1.001 <= kap <= -0.999)
        ga = ga and ok_A
        topM, lam_min_Z = float(evM[-1]), float(evZ[0])
        if (a, K) == (2.0, 8):
            ok_B = abs(topM - (-kap * lam_min_Z)) <= 1e-6
        else:
            ok_B = abs(topM) <= 1e-5 and abs(kap * lam_min_Z) <= 1e-5
        gb = gb and ok_B
        tail_note.append("WITH-tail" if resid < resid_d else "tail-DEGRADED")
        print(f"cell (a={a:g},K={K}): kappa={kap:+.6f} resid={resid:.2e} "
              f"(G-A {'PASS' if ok_A else 'FAIL'}) | discrete-only: "
              f"kappa={kap_d:+.6f} resid={resid_d:.2e} | topM={topM:+.2e} "
              f"kappa*lam_min(Z)={kap * lam_min_Z:+.2e} (G-B {'PASS' if ok_B else 'FAIL'})")
    print(f"G-A identity residuals: {'PASS' if ga else 'FAIL'}   "
          f"tail dependence: {tail_note}")
    print(f"G-B pin-depth mechanism: {'PASS' if gb else 'FAIL'}")

    # ---- G-C: P-2 replication (their variant logic, our capture) ---------
    a, K = 4.0, 8
    t, h, coeffs, basis = f0.null_setup(a, K)
    funcs = coeffs.T @ basis
    A = f0.arch_matrix(funcs, h)
    shifts, weights = f3_random.true_pairs(a)
    m = len(shifts)
    top_of = lambda Pm: float(symev(A + Pm)[-1])
    gc = True
    for variant in ["2a-perm", "2b-unif", "2c-rndw"]:
        got = []
        for seed in range(1, 6):
            rng = np.random.default_rng(seed)
            if variant == "2a-perm":
                perm = rng.permutation(m)
                sh_c = [shifts[perm[j]] for j in range(m)]
                w_c = list(weights)
            elif variant == "2b-unif":
                sh_c = list(rng.uniform(0.0, 2.0 * a, size=m))
                w_c = list(weights)
            else:
                sh_c = list(shifts)
                rr = rng.random(m)
                w_c = list(rr * sum(weights) / rr.sum())
            Pc = f0.prime_matrix(funcs, coeffs, basis, t, h, a, K, sh_c, w_c)
            got.append(top_of(Pc))
        diffs = [abs(g - ref) for g, ref in zip(got, P2_REF[variant])]
        ok = max(diffs) <= 5e-3 and min(got) >= 0.95
        gc = gc and ok
        print(f"P-2 {variant}: got " + ", ".join(f"{x:+.3f}" for x in got)
              + f"  max|got-ref|={max(diffs):.1e}  {'PASS' if ok else 'FAIL'}")
    print(f"G-C P-2 replication (all>=+0.95 and within 5e-3 of reported): "
          f"{'PASS' if gc else 'FAIL'}")

    # ---- G-D: mechanism column at (2,8) -----------------------------------
    r = p6_weil.zero_gram(2.0, 8)
    A2, funcs2, t2, h2 = r["A"], r["funcs"], r["t"], r["h"]
    evA2, vecA2 = eigh((A2 + A2.T) / 2.0)
    vA = vecA2[:, -1]
    vA_grid = vA @ funcs2
    quad = f0.simpson(len(t2), h2)
    m1 = abs((quad * np.exp(1j * GAM1 * t2)) @ vA_grid) ** 2
    top_arch = float(evA2[-1])
    P2m = r["P"]
    eps = -float(symev(P2m)[0]) / top_arch - 1.0
    ratio = eps * top_arch / (2.0 * m1)
    gd = 0.8 <= ratio <= 2.0
    print(f"G-D mechanism: eps={eps:+.3e} A={top_arch:+.6f} m1={m1:.3e} "
          f"ratio={ratio:+.3f} (band [0.8,2.0]) => {'PASS' if gd else 'FAIL'}")

    print(f"\nVERDICT: {'PASS' if (ga and gb and gc and gd) else 'FAIL'}  "
          f"G-A={ga} G-B={gb} G-C={gc} G-D={gd}")
    print("DONE")


if __name__ == "__main__":
    main()
