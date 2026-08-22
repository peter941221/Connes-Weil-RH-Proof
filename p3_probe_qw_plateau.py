#!/usr/bin/env python3
"""P3-0 numerical probe: does qw(bumpPlateauTest) equal 0?

Purpose (Program P, Route B windowing): the proven identity
    ReTr(A_n^* A_n) = 2*log(n+2)*bumpA      for EVERY n   (C1Stage3WindowedTraceP2.lean:106)
means any bulk-subtracted remainder is IDENTICALLY zero on g0, so the P3
readback obligation "renormalized trace -> qw g0" collapses to "0 =? qw g0".

This script evaluates
    qw g0 = poleTerm(F) - archimedeanTerm(F) - finitePrimeSum(F),   F = g0 * g0
using ONLY the explicit definitions in the repo (evidence below). Two
resolutions are run for every quadrature; their difference is reported as an
error estimate.

Evidence / source of each formula:
  bumpEx(x)      Wall14PlateauExplicit.lean:37   = 1 - smoothTransition((x^2-bSq)/(1-bSq))
  smoothTrans.   mathlib SmoothTransition.lean:146,39  glue/(glue+glue(1-x)); glue(u)=e^{-1/u} if u>0 else 0
  F = convSquare CompactLogConvolution.lean:97-112  F(x) = int star(g(-t)) g(x-t) dt; real-even g => (g*g)(x)
  poleTerm       C1SameOwnerWeil.lean:31         Re[laplaceAt(F,1/2)+laplaceAt(F,-1/2)]
  laplaceAt      CC20YoshidaConvolution.lean:55  int e^{s x} F(x) dx; separable => M(s)^2, M(s)=int e^{sx}g(x)dx
  archTerm       C1SameOwnerWeil.lean:61-70      (log(4*pi)+gamma)*F(0) + Re int_{y>0} [e^{y/2}(F(y)+F(-y))-2F(0)]/(e^y-e^{-y}) dy
  denom          SelectedWeilFormula.lean:103    e^y - e^{-y} = 2 sinh y
  primeSum       C1SameOwnerWeil.lean:161        sum_{n in P} Lambda(n)/sqrt(n)*(F(log n)+F(-log n)), P = visible prime powers; F even real => 2*sum Lambda/sqrt*n * F(log n); supp(F) subset [-2,2] => n in {2,3,4,5,7}
  qw             C1SameOwnerWeil.lean:196-201    psi(g.convolutionSquare), psi = pole - arch - prime
"""
import numpy as np

BSQ = (0.9) ** 2          # bSq = (9/10)^2, Wall14PlateauExplicit.lean:24


def glue(u):
    return np.exp(-1.0 / u) if u > 0 else 0.0


def smooth_transition(x):
    a = glue(x)
    b = glue(1.0 - x)
    return a / (a + b)


def bumpEx(x):
    # vectorized; matches Wall14PlateauExplicit.lean:37 exactly
    u = (x * x - BSQ) / (1.0 - BSQ)
    if np.ndim(u) == 0:
        return float(1.0 - smooth_transition(float(u)))
    out = np.empty_like(np.asarray(x, dtype=float))
    uu = np.asarray(u, dtype=float)
    m0 = uu <= 0
    m1 = uu >= 1
    mid = ~(m0 | m1)
    out[m0] = 1.0          # smoothTransition = 0 for u <= 0
    out[m1] = 0.0          # smoothTransition = 1 for u >= 1
    if np.any(mid):
        um = uu[mid]
        a = np.exp(-1.0 / um)
        b = np.exp(-1.0 / (1.0 - um))
        out[mid] = 1.0 - a / (a + b)
    return out


def trapz(f, a, b, n):
    x = np.linspace(a, b, n)
    y = f(x)
    h = (b - a) / (n - 1)
    return float(h * (0.5 * y[0] + y[1:-1].sum() + 0.5 * y[-1]))


def F_at(x, n):
    """Direct quadrature of F(x) = int bumpEx(t)*bumpEx(x-t) dt; integrand support in [x-1,x+1] cap [-1,1]."""
    lo = max(-1.0, x - 1.0)
    hi = min(1.0, x + 1.0)
    if hi <= lo:
        return 0.0

    def integrand(t):
        return bumpEx(t) * bumpEx(x - t)

    return trapz(integrand, lo, hi, n)


def F_grid_fft(nfft, half_len=4.0):
    """F on a uniform grid over [-half_len, half_len) via zero-padded linear convolution.

    The FFT origin must sit at position 0 so the support [-1,1] straddles index 0 and the
    circular convolution has no wrap-around contamination (support width N/2 < period N).
    """
    h = 2 * half_len / nfft
    j = np.arange(nfft)
    pos_shifted = ((j + nfft // 2) % nfft) * h - half_len   # index k <-> position; pos(k=0)=0
    g = bumpEx(pos_shifted)
    G = np.fft.rfft(g, n=nfft)
    conv = h * np.fft.irfft(G * G, n=nfft)                  # conv[k] ~ F(pos(k)) for |pos| < 2
    xs = -half_len + j * h                                  # monotone grid for interpolation
    Fvals = conv[(j - nfft // 2) % nfft]                    # re-index onto the monotone grid
    return xs, Fvals


def probe(res_lo, res_hi, nfft):
    # (a) M(1/2) -> poleTerm(F) = 2*M(1/2)^2   [F real even: M(-1/2)=M(1/2); Re of real square]
    def m_half(x):
        return np.exp(0.5 * x) * bumpEx(x)

    M_lo = trapz(m_half, -1.0, 1.0, res_lo)
    M_hi = trapz(m_half, -1.0, 1.0, res_hi)
    pole_lo = 2.0 * M_lo ** 2
    pole_hi = 2.0 * M_hi ** 2

    # (b) F(0) = bumpA = int g^2
    def g2(x):
        return bumpEx(x) ** 2

    F0_lo = trapz(g2, -1.0, 1.0, res_lo)
    F0_hi = trapz(g2, -1.0, 1.0, res_hi)

    # (c) archimedean main integral over [0,2]; combined integrand smooth at 0 with limit F(0)/2
    xg, Fgrid = F_grid_fft(nfft)

    def arch_integrand(y):
        yv = np.asarray(y, dtype=float)
        Fy = np.interp(yv, xg, Fgrid)   # F even: F(-y)=F(y); grid covers [0,2] interior
        den = 2.0 * np.sinh(yv)   # e^y - e^{-y} exactly; expm1(y)-exp(-y) would be off by 1
        num = 2.0 * np.exp(0.5 * yv) * Fy - 2.0 * F0_hi
        out = np.empty_like(yv)
        m0 = yv == 0.0
        out[~m0] = num[~m0] / den[~m0]
        out[m0] = F0_hi / 2.0            # analytic limit derived in the probe notes
        return out

    I_main_lo = trapz(arch_integrand, 0.0, 2.0, res_lo)
    I_main_hi = trapz(arch_integrand, 0.0, 2.0, res_hi)

    # (d) tail: -2*F(0)*int_2^inf dy/(e^y-e^{-y}); antiderivative 1/2 ln tanh(y/2):
    # int_a^inf dy/(2 sinh y) = atanh(e^{-a})   [equivalently sum_k e^{-(2k+1)a}/(2k+1)]
    tail_const = float(np.arctanh(np.exp(-2.0)))

    # (e) finite prime sum: visible n in {2,3,4,5,7} (|log n| < 2); even real F => factor 2
    primes = [(2, np.log(2)), (3, np.log(3)), (4, np.log(2)), (5, np.log(5)), (7, np.log(7))]
    prime_sum_hi = 0.0
    fft_vals, direct_vals = [], []
    for n, ln in primes:
        fd = F_at(ln, res_hi)                    # direct quadrature (primary)
        ff = float(np.interp(ln, xg, Fgrid))     # FFT cross-check
        prime_sum_hi += 2.0 * (ln / np.sqrt(n)) * fd
        fft_vals.append(ff)
        direct_vals.append(fd)

    arch_lo = (np.log(4 * np.pi) + 0.57721566490153286060) * F0_lo + I_main_lo - 2.0 * F0_lo * tail_const
    arch_hi = (np.log(4 * np.pi) + 0.57721566490153286060) * F0_hi + I_main_hi - 2.0 * F0_hi * tail_const

    qw_lo = pole_lo - arch_lo - prime_sum_hi
    qw_hi = pole_hi - arch_hi - prime_sum_hi

    return dict(M=(M_lo, M_hi), F0=(F0_lo, F0_hi), pole=(pole_lo, pole_hi),
                I_main=(I_main_lo, I_main_hi), arch=(arch_lo, arch_hi),
                prime_sum=prime_sum_hi, qw=(qw_lo, qw_hi),
                fft_vals=fft_vals, direct_vals=direct_vals)


def main():
    r = probe(1 << 15, 1 << 16, nfft=1 << 20)

    def row(name, lo, hi):
        print(f"{name:<14} {lo:+.12e}   {hi:+.12e}   d={abs(hi-lo):.3e}")

    print("== P3-0 probe: qw(bumpPlateauTest) decomposition ==")
    row("M(1/2)", *r["M"])
    row("F(0)=bumpA", *r["F0"])
    assert r["F0"][1] >= 1.8 - 1e-6, "sanity: bumpA >= 9/5 (Wall14PlateauExplicitComplex.lean:152)"
    row("poleTerm", *r["pole"])
    row("I_main[0,2]", *r["I_main"])
    row("archTerm", *r["arch"])
    print(f"{'primeSum':<14} {r['prime_sum']:+.12e}")
    row("qw", *r["qw"])

    n = [2, 3, 4, 5, 7]
    for i, nn in enumerate(n):
        print(f"F(log {nn}): direct={r['direct_vals'][i]:+.9e}  fft={r['fft_vals'][i]:+.9e}  d={abs(r['direct_vals'][i]-r['fft_vals'][i]):.2e}")

    qw = r["qw"][1]
    err = abs(r["pole"][0] - r["pole"][1]) + abs(r["arch"][0] - r["arch"][1]) + 3e-9
    print(f"\nVERDICT: qw g0 = {qw:+.6e}   (error est ~{err:.1e})")
    if abs(qw) > max(5 * err, 1e-7):
        print("FORK B: qw g0 != 0  -> plain bulk subtraction leaves a nonzero gap; P3 needs a refined correction / different operator piece.")
    else:
        print("FORK A (tentative): |qw g0| within numerical error -> escalate to mpmath/Lean exactness before committing.")


if __name__ == "__main__":
    main()
