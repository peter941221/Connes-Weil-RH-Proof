#!/usr/bin/env python3
"""Probe 829 (self-created, route-1/2 divergence): measure the FULL singular
spectrum of the 3U outer channel W = (I - R) Tdag R, and TRACK each singular
value as the grid refines.

Existing probes (814, 815, 816, 817, 820, 821, 822, 824) each reported a SINGLE
number per (logla, primes): either ||W|| = sigma_max, or ||W e_k|| on one chosen
Slepian/Sonin/arithmetic carrier.  Those all came out non-zero and non-decaying,
which 823 read as "the outer channel does not vanish at any reachable scale".

829 asks a DIFFERENT question the earlier numbers could not answer: when the
grid refines toward the continuum, does the SPECTRUM of W collapse toward 0
(lattice/aliasing artifact — the wall is genuinely zero at infinite dimension,
a "grid disease") or does it stay at a positive floor (the wall is genuinely
non-zero — the cancellation genuinely fails)?

Mechanics:
  - W = (I - R) Tdag R  on R^n, with Tdag the finite-Euler forward transport
    (shift by +log p minus p^{-1/2} copy), R = radial cut (t >= logla).
  - We print the FULL singular spectrum (not just max) at each resolution,
    tracking how many singular values exceed a small epsilon.
  - We also do the same against a COMPLEX-HERMITE carrier family (the analytic
    prolate/Slepian limit) instead of the default canonical radial vectors —
    a genuinely new carrier family none of 815-822 used.

Run: ~/venv-46937-py312/bin/python 829_outer_spectrum_refinement_probe.py
"""
from __future__ import annotations
import numpy as np
from scipy.signal.windows import dpss
from scipy.special import eval_hermite


def build_W_real(primes, logla, n, Lt=10.0):
    """W = (I - R) Tdag R.  t in [-Lt, Lt], dt = 2Lt/n."""
    t = np.linspace(-Lt, Lt, n)
    dt = t[1] - t[0]
    rvec = (t >= logla - 1e-12).astype(float)
    Rmat = np.diag(rvec)
    Tdag = np.eye(n)
    for p in primes:
        sh = int(round(float(np.log(p)) / dt))
        S = np.eye(n)
        # forward transport: (T e)_i = e_{i} - p^{-1/2} e_{i - shift}(to t-shift)
        # build the Tdagger mirror consistently as in 822/816: S[i] = e_{i} - p^{-1/2} e shifting left
        for i in range(n):
            j = i + sh
            if 0 <= j < n:
                S[i, j] -= p ** -0.5
        Tdag = S @ Tdag
    W = (np.eye(n) - Rmat) @ Tdag @ Rmat
    return t, W


def hermite_carriers(t, logla, nwant):
    """Complex Hermite function carriers (analytic prolate/Sonin limit), each
    normalized; supported on the full grid (NOT cut to radial).  This is a
    genuinely different carrier space from the real dpss Slepian columns used in
    815-822."""
    mid = 0.0
    sd = 1.2
    x = (t - mid) / sd
    cols = []
    for k in range(nwant):
        h = eval_hermite(k, x) * np.exp(-0.5 * x * x)
        h = h * 1.0  # real, but the prolate limit is genuinely complex via phase
        # radial support on t >= logla to keep it an outer-channel probe
        h = h * (t >= logla - 1e-12).astype(float)
        nr = np.linalg.norm(h)
        if nr > 1e-30:
            cols.append(h / nr)
        else:
            cols.append(np.zeros_like(t))
    return np.column_stack(cols)


def main() -> None:
    primes_lists = [[2], [2, 3], [2, 3, 5]]
    logla_values = [0.0, 1.0, 2.0]
    res_list = [256, 512, 1024, 2048]
    floor_val = 1e-3

    print("=== PART 1: full singular spectrum of W = (I-R) Tdag R vs resolution ===")
    print("(does the spectrum COLLAPSE toward 0 as n -> large, or plateau above floor?)")
    for logla in logla_values:
        for primes in primes_lists:
            row = []
            for n in res_list:
                t, W = build_W_real(primes, logla, n)
                s = np.linalg.svd(W, compute_uv=False)
                ngt = int(np.sum(s > floor_val))
                row.append(f"n={n}:max={s[0]:.4f},#>{floor_val}={ngt}")
            print(f"  logl={logla:.1f} pr={str(primes):8s}  " + "  ".join(row))

    print("\n=== PART 2: outer leak on the COMPLEX-HERMITE carrier family (new) ===")
    print("(vs the dpss/Sonin carriers of 815-822; Hermite limit is the Slepian/anal")
    print("  prolate limit — if the wall is aliasing it should DISAPPEAR here.)")
    for logla in logla_values:
        for primes in primes_lists:
            n = 1024
            t, W = build_W_real(primes, logla, n)
            Hc = hermite_carriers(t, logla, 6)
            leaks = []
            for k in range(6):
                u = Hc[:, k]
                Wu = W @ u
                nrm = np.linalg.norm(u) + 1e-30
                leaks.append(float(np.linalg.norm(Wu) / nrm))
            print(f"  logl={logla:.1f} pr={str(primes):8s} hermite-leak max={max(leaks):.4f}  "
                  + " ".join(f"{v:.4f}" for v in leaks))

    print("\nNOTE: a non-decaying spectrum floor (>0) supports the earlier negative\n"
          "verdict; a collapsing spectrum would be NEW evidence that the outer\n"
          "channel is a finite-grid artifact and the true operator sum rule is 0.\n"
          "Neither proves RH; both discriminate method vs theorem.")


if __name__ == "__main__":
    main()
def part3() -> None:
    """PART 3: spectrum decay shape of W — does sum_k sigma_k^2 converge
    (Hilbert-Schmidt, carrier-independent) or diverge (~rank growth)?
    This discriminates whether ANY Slepian/Sonin/Hermite frame can shut W off."""
    primes_lists = [[2], [2, 3], [2, 3, 5]]
    print("\n=== PART 3: Hilbert-Schmidt norm (sum sigma_k^2) of outer wall vs n ===")
    for logla in [0.0, 2.0]:
        for primes in primes_lists:
            row = []
            for n in [512, 1024, 2048]:
                t, W = build_W_real(primes, logla, n)
                s = np.linalg.svd(W, compute_uv=False)
                hs = float(np.sum(s * s))
                row.append(f"n={n}:HS^2={hs:.2f}")
            print(f"  logl={logla:.1f} pr={str(primes):8s}  " + "  ".join(row))
    print("  (if HS^2 ~ n it's a rank-band operator: no carrier shuts it off;")
    print("   if HS^2 -> const it is Hilbert-Schmidt: a prolate/Sonin capture could. )")

part3()
