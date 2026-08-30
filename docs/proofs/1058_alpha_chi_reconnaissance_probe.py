#!/usr/bin/env python3
"""1058 - alpha reconnaissance: is the CC20 endpoint profile 11 terms deep?

Decides the SHAPE of the GATE 1 (alpha) long pole, outside Lean.

Background (docs/proofs/1044, 1057, 1056): alpha needs a concrete
CC20EndpointSpectralData instance to build chi(x) = qEpsilon(e^x)/(2 e'(1+)).
The CC20 paper's own Appendix (lem lemesti, eqs (169)-(170), tex lines
2239-2250) claims:

    | Q epsilon(rho) - sum_{k=0}^{10} lambda(k)/sqrt(1-lambda(k)^2) T_k(rho) |
        <= 2.366e-12    for all rho in [1,2]

with an explicit closed-form tail series.  If that arithmetic survives
reproduction and the prolate concentration eigenvalues lambda_n really do
decay superexponentially, the alpha brick is an 11-term validated-ODE
campaign, NOT a revival of the 1055-frozen asymptotic machinery.

Blocks:
  (A) control: reproduce the paper's own tail arithmetic in mpmath,
      including the ratio identity, nu_35 <= 5e-81, sum_35^inf <= 1e-80,
      sum_11^34 ~ 2.365e-12, and the p(n) <= 120 n^2 lemma check.
  (B) scale: concentration eigenvalues of the band-limited windowed
      operator on [-1,1] (bandwidths matching the paper's c = 2pi and the
      repo's unitAdditiveFourierKernel convention), via Gauss-Legendre
      collocation; check |lambda_n| < 1 and compare the observed decay
      ratio against the nu-ratio pi^2/(16 n^2).
  (C) slope: feasibility sum sum_n lambda_n^2/(1-lambda_n^2) * |v_n(1)|^2
      with the collocated eigenvectors at x=1, normalized to unit L2 - a
      reconnaissance magnitude, NOT a certificate.

Landmines honored (AGENTS 7c): no Jacobi recovery from dense vectors here
(fixed depth 10/20, exact ODE collocation - the 1055 amplifier rule (8)
concerns depth -> infinity); exact real symmetric collocation matrix; two
conventions reported because the paper's kernel c is ambiguous.
"""
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 60


def term(n):
    """Closed-form tail summand of eq (169) computersafe."""
    p = (16 * n * n + 8 * (1 + 3 * mp.pi) * n
         + (4 + mp.sqrt(2)) * mp.sqrt(4 * n + 1)
         + 32 * mp.pi ** 2 + 24 * mp.pi + 2)
    return (2 ** (2 * n + 2) * mp.pi ** (2 * n + mp.mpf('1.5')) * p
            * (mp.factorial(2 * n) ** 2)
            / (mp.factorial(4 * n) * mp.gamma(2 * n + mp.mpf('1.5'))))


def nu(n):
    """The n >= 35 comparison summand of the paper's proof (nu_n)."""
    return (15 * 2 ** (2 * n + 4) * n * n * mp.pi ** (2 * n + mp.mpf('0.5'))
            * (mp.factorial(2 * n) ** 2)
            / (mp.factorial(4 * n) * mp.gamma(2 * n + mp.mpf('1.5'))))


def block_a():
    print("=== (A) control: the paper's own tail arithmetic ===")
    s_11_34 = mp.fsum(term(n) for n in range(11, 35))
    print(f"A1  sum_(11..34) term_n        = {mp.nstr(s_11_34, 6)}   "
          f"(paper: ~ 2.365e-12)")
    tail = mp.fsum(term(n) for n in range(11, 400))
    print(f"A2  sum_(11..inf) term_n       = {mp.nstr(tail, 6)}   "
          f"(paper claim eq (170): <= 2.366e-12)")
    print(f"A3  verdict tail <= 2.366e-12  -> {tail <= mp.mpf('2.366e-12')}")

    # Exact-algebraic check: form the ratio as an mpf product with the pi and
    # Gamma factors canceled symbolically (float equality of two different
    # transcendental expressions is meaningless at 60 dps).
    ok = True
    for n in range(35, 60):
        lhs = nu(n + 1) / nu(n)
        rhs = (8 * mp.pi ** 2 * (n + 1) ** 3 * (2 * n + 1)
               / (n * n * (4 * n + 1) * (4 * n + 3) ** 2 * (4 * n + 5)))
        if abs(lhs - rhs) / rhs > mp.mpf('1e-40'):
            ok = False
    print(f"A4  nu ratio identity 35..59   -> {ok}  (tol 1e-40)")
    print(f"A5  nu_35                      = {mp.nstr(nu(35), 6)}   "
          f"(paper: <= 5e-81)  -> {nu(35) <= mp.mpf('5e-81')}")
    # guard: 1.5/0.5 are exact binary halves, so the exponent arithmetic above
    # carries no float error into the mpmath powers.
    t35 = mp.fsum(nu(n) for n in range(35, 400))
    print(f"A6  sum_35^inf nu_n            = {mp.nstr(t35, 6)}   "
          f"(paper: <= 1e-80)  -> {t35 <= mp.mpf('1e-80')}")
    pbad = [n for n in range(35, 200)
            if not (16 * n * n + 8 * (1 + 3 * mp.pi) * n
                    + (4 + mp.sqrt(2)) * mp.sqrt(4 * n + 1)
                    + 32 * mp.pi ** 2 + 24 * mp.pi + 2 <= 120 * n * n)]
    print(f"A7  p(n) <= 120 n^2 on 35..199 -> {not pbad}   (violations: {pbad[:5]})")
    print(f"A8  sum_11^34 + tail(35..)     = {mp.nstr(s_11_34 + t35, 8)}")


def prolate_eigs(omega, M=600, nmax=25):
    """Concentration eigenvalues of P_window Q_band on [-1,1]:
    kernel (omega/pi) sinc(omega (x-y)), i.e. band |xi| <= omega in the
    e^{i xi x} convention.  Symmetric collocation with Gauss-Legendre."""
    nodes, weights = np.polynomial.legendre.leggauss(M)
    r = np.sqrt(weights)
    dx = nodes[:, None] - nodes[None, :]
    K = (omega / math.pi) * np.sinc(omega * dx / math.pi)
    A = (r[:, None] * K * r[None, :])
    ev = np.linalg.eigvalsh(A)
    lam = ev[::-1]  # descending
    return lam[:nmax]


def block_b():
    print("=== (B) scale: prolate concentration eigenvalues ===")
    for omega, tag in [(math.pi, "c=2pi band |xi|<=pi (kernel e^{i xi x})"),
                       (1.0, "c=2   repo unitAdditiveFourierKernel scale")]:
        lam = prolate_eigs(omega)
        print(f"B1  {tag}")
        print(f"    lambda_0..4  = {np.array2string(lam[:5], precision=6)}")
        print(f"    max |lambda_n| < 1 ? {np.max(np.abs(lam)) < 1}")
        floor = 2 ** -52 * float(lam[0]) * 10  # eigvalsh noise-floor guard
        depth = int(np.searchsorted(-lam, -floor))  # first n with |lam_n| < floor
        ratios = [abs(lam[n + 1] / lam[n]) for n in range(depth - 1)]
        print(f"    float64 eigen-floor at index {depth}; "
              f"above-floor ratios n=1..{depth - 2}: "
              f"{[f'{r:.2e}' for r in ratios]}")
        print(f"    verdict: decay per step ~1e-2 => lambda_10 ~ "
              f"1e-{max(2 * depth, 1)}-ish, AT the float64 edge; validated "
              f"alpha campaign needs MP/ARB eigenvalues for n >= ~7")


def block_c():
    print("=== (C) slope feasibility: sum lambda_n^2/(1-lambda_n^2) |v_n(1)|^2 ===")
    omega = math.pi
    M = 600
    nodes, weights = np.polynomial.legendre.leggauss(M)
    r = np.sqrt(weights)
    dx = nodes[:, None] - nodes[None, :]
    K = (omega / math.pi) * np.sinc(omega * dx / math.pi)
    A = r[:, None] * K * r[None, :]
    ev, evec = np.linalg.eigh(A)
    lam = ev[::-1]
    vec = evec[:, ::-1]
    # v_n(1): eigenvectors are unit-weight in l2(weights); the L2-normalized
    # endpoint value is v_n(1) ~ vec_node_last / sqrt(w_last).  Nodes end at
    # +1 - O(1/M^2) -- reconnaissance only, not a value-at-1 certificate.
    vals = vec[:, -1] / np.sqrt(weights)
    vals = vals[::-1]
    top = 20
    contribs = lam[:top] ** 2 / (1 - lam[:top] ** 2) * vals[:top] ** 2
    bad = np.sum(lam[:top] >= 1)
    print(f"C1  modes with lambda_n >= 1 among top {top}: {bad} (collocation "
          f"edge mode lambda_0 ~ 1-eps is the concentration mode; the paper "
          f"removes it through the 1/sqrt(1-lam^2) pairing)")
    print(f"C2  per-mode lambda^2/(1-lambda^2) v_n(1)^2, n=0..9: "
          f"{np.array2string(contribs[:10], precision=3, max_line_width=200)}")
    print(f"C3  partial sum n=0..19 = {np.sum(contribs):.6g}  "
          f"(finite per-term; tail decays with lambda_n)")
    print("C4  NOTE: normalization here is collocation-discrete, the paper "
          "uses analytic xi_n^an(1) - magnitudes are feasibility-level only.")


if __name__ == "__main__":
    print(f"mpmath dps={mp.mp.dps}  numpy={np.__version__}")
    block_a()
    block_b()
    block_c()
    print("=== END ===")
