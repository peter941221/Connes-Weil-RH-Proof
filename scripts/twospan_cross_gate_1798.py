#!/usr/bin/env python3
# twospan_cross_gate_1798.py — record 1798
#
# First cross-gate pricing rig for the two-span C3 producer.
#
# Committed definitions coded verbatim (F27/F28: source read before rig):
#   pairTest        (A*⋆B)(x) = ∫ conj(A(−t))·B(x−t) dt
#                     [CCM25Concrete.CompactLogConvolution, convolution_apply]
#   archimedeanTerm F = Re[(log 4π + γ)·F(0)
#                          + ∫_0^∞ (e^{y/2}(F(y)+F(−y)) − 2F(0))
#                                   / (e^y − e^{−y}) dy]
#                     [C1SameOwnerWeil : archimedeanNumerator / archimedeanTerm]
#   finitePrimeTerm F n = Re[Λ(n)·n^{−1/2}·(F(log n)+F(−log n))]
#                     [C1SameOwnerWeil : finitePrimeTermComplex]
#   ICgate F = archimedeanTerm F + finitePrimeSum F
#                     [C1LocalConfigurationDomination :73]
#   q-form = IC(A*⋆A) + λ²·IC(B*⋆B) − λ·(IC(A*⋆B)+IC(B*⋆A))
#                     [C1P2SpanProfileMatrix : twoSpan_gate_qform_expand]
#
# Laws honored:
#   F74: denominator is e^y − e^{−y} (NOT expm1(2y)).
#   F71: three-way validation on every readout class.
#   F77: four-engine agreement; any engine split = instrument death.
#   F75: σ-identity oversampling dξ ≤ 0.05.
#
# Scope (record 1798): price the three gate entries, the swap symmetry,
# the q-form face (det, roots, free minimum), the pinned-λ face from the
# detector-node interpolation condition, and the per-prime-power binding
# chart.  The full OrbitG8Geometry interpolation system (orbit sum = −2,
# ball zero control, dyadic tail budget) is NOT instantiated here.

import json
import math
import os
import sys
import time

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline

try:
    import mpmath as mp
    HAVE_MP = True
except Exception:
    HAVE_MP = False

LOGPI = math.log(math.pi)
LOG4PI_GAMMA = math.log(4.0 * math.pi) + 0.5772156649015329
LOG2 = math.log(2.0)

# ---------------------------------------------------------------- logging

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ----------------------------------------------------------------- grids

LX = 6.0            # half-width of the working grid
DU = 5.0e-4         # working grid step
N = int(round(2 * LX / DU)) + 1
XG = -LX + np.arange(N) * DU
NF = 65536          # padded FFT length (>= 2N for linear convolution)

# refined grid for Laplace reads at exact complex points
DUS = 2.0e-4
NS = int(round(2 * LX / DUS)) + 1
XGS = -LX + np.arange(NS) * DUS


def bump(c):
    """C^∞ compact bump supported exactly on [−c, c]."""
    x = XG
    f = np.zeros_like(x)
    m = np.abs(x) < c
    xm = x[m]
    f[m] = np.exp(-1.0 / (1.0 - (xm / c) ** 2))
    return f


def spectral_deriv(f, order):
    """d^order/dx^order on the uniform grid via padded FFT (periodized;
    support interior so wrap-around is negligible)."""
    F = np.fft.fft(f, NF)
    xi = 2.0 * np.pi * np.fft.fftfreq(NF, d=DU)   # angular frequency
    out = F
    for _ in range(order):
        out = out * (1j * xi)
    g = np.real(np.fft.ifft(out))[:N]
    return g


def laplace_grid(f, s, xgrid):
    """∫ f(x) e^{−s x} dx by rectangle rule (f vanishes at the ends)."""
    return DUS * complex(np.sum(f * np.exp(-s * XGS))) if len(f) == len(XGS) \
        else DU * complex(np.sum(f * np.exp(-s * xgrid)))


def laplace_spline(sp, s):
    """∫ F(x) e^{−s x} dx via spline resampling on the refined grid."""
    vals = sp(XGS)
    return DUS * complex(np.sum(vals * np.exp(-s * XGS)))


# ------------------------------------------------------- pair-test engines

def pair_direct(A, B):
    """E1: F(x) = ∫ conj(A(−t))·B(x−t) dt by explicit convolution.

    full[m] = Σ_k c[k]B[m−k] lives at x = x_c[0] + x_B[0] + m·du = −2LX + m·du;
    F(x_j) = du·full[j + (N−1)/2]  (j = (N−1)/2 is x = 0)."""
    c = np.conj(A[::-1])
    full = DU * np.convolve(c, B, mode="full")   # length 2N−1
    off = (N - 1) // 2
    return full[off: off + N]


def pair_fft(A, B):
    """E2: same convolution via padded FFT (identical index convention)."""
    c = np.conj(A[::-1])
    Fc = np.fft.fft(c, NF)
    Fb = np.fft.fft(B, NF)
    full = DU * np.fft.ifft(Fc * Fb)
    off = (N - 1) // 2
    return full[off: off + N]


# ------------------------------------------------------------ arch engines

def arch_direct(F, S, tag="", loud=False):
    """E1 arch: y-quadrature of the committed integrand + closed tail.

    The integrand is analytic at 0 with limit Re F(0)/2, so the exact
    formula is integrated from y0 = 1e-8 (numerically stable: numerator
    ~ F0·y cancels the 2y denominator).  The Taylor check
    integrand(y) ≈ F0/2 + (F2/2 + F0/8)y is logged as a sanity witness
    at ys = 0.05 (O(y²) truncation, expect ~1e-3 agreement).

    Returns (arch, imag_residual, series_check_diff)."""
    sp = CubicSpline(XG, F)
    F0 = complex(sp(0.0))
    F2 = float(sp(0.0, nu=2).real)
    ymax = S + 30.0

    def num(y):
        v = complex(sp(y)) + complex(sp(-y))
        return math.exp(y / 2.0) * v - 2.0 * F0

    def integ_r(y):
        return (num(y) / (math.exp(y) - math.exp(-y))).real

    def integ_i(y):
        return (num(y) / (math.exp(y) - math.exp(-y))).imag

    y0 = 1.0e-8
    core_r = quad(integ_r, y0, ymax, limit=800, epsabs=1e-13,
                  epsrel=1e-13, points=[1e-6, 1e-4, 1e-2])[0]
    core_i = quad(integ_i, y0, ymax, limit=800, epsabs=1e-13,
                  epsrel=1e-13, points=[1e-6, 1e-4, 1e-2])[0]
    ys = 0.05
    direct_at_ys = integ_r(ys)
    series_at_ys = F0.real / 2.0 + (F2 / 2.0 + F0.real / 8.0) * ys
    sdiff = direct_at_ys - series_at_ys
    tail = F0.real * math.log(math.tanh(ymax / 2.0))
    arch = LOG4PI_GAMMA * F0.real + core_r + tail
    if loud:
        log("    arch[%s] = %+.12f  (imag residual %.2e, "
            "series/formula agree %.2e)" % (tag, arch, core_i, sdiff))
    return arch, core_i, sdiff


def sigma_vec(om):
    """σ(angle) = log π − Re ψ(¼ − i·angle/2) — 1741 engine VERBATIM."""
    z = 0.25 - 0.5j * np.asarray(om, dtype=complex)
    M = 8
    zz = z + M
    s = np.zeros_like(z)
    for j in range(M):
        s = s + 1.0 / (z + j)
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    zz2 = zz * zz
    corr = np.zeros_like(z)
    pw = zz2.copy()
    for b in terms:
        corr = corr + b / pw
        pw = pw * zz2
    psi = np.log(zz) - 0.5 / zz - corr - s
    return LOGPI - psi.real


def arch_sigma_fft(F, tag="", loud=False):
    """E3 arch: arch(F) = ∫ σ(2πξ) F̂(ξ) dξ, F̂ via padded FFT (F75/F77)."""
    Fp = np.zeros(NF, dtype=complex)
    Fp[:N] = F
    Fh = DU * np.fft.fft(Fp)
    xi = np.fft.fftfreq(NF, d=DU)                # cycles per unit
    # grid offset phase: x_n = n·du − LX  ⟹  F̂(ξ) = du·e^{+2πiξLX}·DFT(F)
    Fh = Fh * np.exp(2j * np.pi * xi * LX)
    sig = sigma_vec(2.0 * np.pi * xi)
    dxi = 1.0 / (NF * DU)
    val = complex(np.sum(sig * Fh)) * dxi
    if loud:
        log("    arch_sigma[%s] = %+.12f" % (tag, val.real))
    return val.real


def arch_sigma_quad_Fhat(Fhat, tag="", loud=False):
    """E3b: same identity with an ANALYTIC F̂ (exact-answer calibration)."""
    s = quad(lambda x: float(sigma_vec(2.0 * math.pi * x)) * Fhat(x),
             -60.0, 60.0, limit=800, epsabs=1e-13, epsrel=1e-13)[0]
    if loud:
        log("    arch_sigma_quad[%s] = %+.12f" % (tag, s))
    return s


# ------------------------------------------------------------ prime reads

def prime_powers_up_to(xmax):
    """All prime powers n ≤ xmax with (n, Λ(n))."""
    out = []
    if xmax < 2:
        return out
    n = int(math.floor(xmax))
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    for p in range(2, n + 1):
        if sieve[p]:
            pk = p
            while pk <= n:
                out.append((pk, math.log(p)))
                pk *= p
    out.sort()
    return out


def prime_sum(Fsp, S):
    """Committed finite prime sum of F over visible prime powers."""
    terms = []
    for n, lam in prime_powers_up_to(math.exp(S)):
        v = complex(Fsp(math.log(n))) + complex(Fsp(-math.log(n)))
        t = lam / math.sqrt(n) * v.real
        terms.append((n, lam, t))
    return sum(t for _, _, t in terms), terms


# ------------------------------------------------------------------ gates

def gate_entry(A, B, S_pair, tag=""):
    """ICgate(A*⋆B) = arch + finite prime sum, four engines."""
    F1 = pair_direct(A, B)
    F2 = pair_fft(A, B)
    split = float(np.max(np.abs(F1 - F2)))
    a1, imres, sdiff = arch_direct(F1, S_pair, tag=tag)
    a3 = arch_sigma_fft(F1, tag=tag)
    sp = CubicSpline(XG, F1)
    psum, terms = prime_sum(sp, S_pair)
    g1 = a1 + psum
    g3 = a3 + psum
    F0 = complex(sp(0.0))
    log("  entry %-14s  arch=%+.9f  sigma_arch=%+.9f  (d=%.2e)  "
        "primes=%+.9f  IC=%+.9f  F0=%.6f maxF=%.3f  conv_split=%.2e  "
        "imag=%.1e  s=%.1e"
        % (tag, a1, a3, a3 - a1, psum, g1, F0.real, np.max(np.abs(F1)),
           split, imres, sdiff))
    return {
        "tag": tag, "arch": a1, "arch_sigma": a3, "prime_sum": psum,
        "IC": g1, "IC_sigma_engine": g3, "conv_split": split,
        "F0": F0.real, "maxF": float(np.max(np.abs(F1))),
        "imag_residual": imres, "series_diff": sdiff,
        "prime_terms": [{"n": n, "lam": lam, "term": t}
                        for n, lam, t in terms],
        "spline": sp,
    }


# -------------------------------------------------------------- D3 roots

def d3_root(h):
    """B = D(D−½)(D−1)h = D³h − 1.5 D²h + 0.5 Dh.
    L[B](s) = s(s−½)(s−1)·L[h](s)  (committed derivativeShift algebra)."""
    h1 = spectral_deriv(h, 1)
    h2 = spectral_deriv(h, 2)
    h3 = spectral_deriv(h, 3)
    return h3 - 1.5 * h2 + 0.5 * h1


def mass_zero(A, psi):
    """A − (∫A/∫ψ)·ψ."""
    m = DU * A.sum() / (DU * psi.sum())
    return A - m * psi, m


def l2_normalize(f):
    """L²(grid) normalize — F52: unnormalized floors report nothing."""
    nrm = math.sqrt(DU * float(np.sum(np.abs(f) ** 2)))
    return f / nrm


# ------------------------------------------------------------- main scan

def main():
    log("record 1798 — first cross-gate pricing (two-span C3 producer)")
    log("grid: N=%d du=%.0e LX=%.1f  padded FFT NF=%d" % (N, DU, LX, NF))

    # ---- V0 instrument calibration on exact-answer families (F43/F52)
    log("V0: Gaussian exact-answer calibration")
    c = 2.0
    gaus = np.exp(-np.pi * XG ** 2)
    gaus[np.abs(XG) > 3.0] = 0.0
    a1, _, _ = arch_direct(gaus, 3.0, tag="gauss")
    a3 = arch_sigma_quad_Fhat(lambda x: math.exp(-math.pi * x * x),
                              tag="gauss-exactFhat")
    # for F = gaussian, Fpair(y) = 2F(y); committed integrand uses F(y)+F(−y)
    log("  V0 gaussian: arch_direct=%.12f arch_sigma(exact Fhat)=%.12f "
        "diff=%.2e" % (a1, a3, a1 - a3))

    # ---- families (all L²-normalized: F52)
    log("building families (all L2-normalized)")
    RA = 1.8
    A_head = l2_normalize(bump(RA * 0.5))      # head at radius 0.9
    A_big = l2_normalize(bump(RA))             # big head radius 1.8
    psi_wide = bump(1.95)
    A_raw = bump(RA)
    A_big_mz, mz_amt = mass_zero(A_raw, psi_wide)
    A_big_mz = l2_normalize(A_big_mz)
    log("  mass-zero projection amount = %.6f" % mz_amt)

    w_root = LOG2 / 2                          # ROOT window 0.34657
    B_D3_raw = d3_root(bump(w_root))
    B_D3 = l2_normalize(B_D3_raw)
    B_win = l2_normalize(bump(0.30))           # plain window bump (contrast)
    A_D3 = l2_normalize(d3_root(bump(0.9)))    # D3 head (vanishing head)
    log("  family peaks: A_head=%.3f A_big=%.3f B_D3=%.3f B_win=%.3f"
        % (np.max(np.abs(A_head)), np.max(np.abs(A_big)),
           np.max(np.abs(B_D3)), np.max(np.abs(B_win))))

    # D3 transform check: L[B](s) = s(s−½)(s−1) L[h](s)  (pre-normalization)
    h = bump(w_root)
    hs = CubicSpline(XG, h)
    bs = CubicSpline(XG, B_D3_raw)
    for s in (0.25 + 0.0j, 1.0 + 3.0j, 1.5 + 14.1347j):
        lb = laplace_spline(bs, s)
        lh = laplace_spline(hs, s)
        pred = s * (s - 0.5) * (s - 1.0) * lh
        log("  D3 check L[B](%.2f%+.2fj): rig=%s pred=%s rel=%.1e"
            % (s.real, s.imag, complex(lb), complex(pred),
               abs(lb - pred) / max(1e-300, abs(pred))))

    rows = []

    # ---- pairs to price (head A, reference B)
    heads = [
        ("head_bump0.9", A_head),
        ("head_bump1.8", A_big),
        ("head_bump1.8_mz", A_big_mz),
        ("head_D3_0.9", A_D3),
    ]
    refs = [
        ("ref_D3_root", B_D3),
        ("ref_winbump0.3", B_win),
    ]

    for ha, A in heads:
        for rb, B in refs:
            tag = ha + " x " + rb
            log("pair: %s" % tag)
            SA = 1.95 if "mz" in ha else (RA if "1.8" in ha else 0.95)
            SB = w_root if "D3" in rb else 0.30
            S_pair = SA + SB
            gA = gate_entry(A, A, 2 * SA, tag="AA:" + ha)
            gB = gate_entry(B, B, 2 * SB, tag="BB:" + rb)
            gAB = gate_entry(A, B, S_pair, tag="AB:" + tag)
            # swap symmetry check: IC(B*⋆A) should equal IC(A*⋆B)
            gBA = gate_entry(B, A, S_pair, tag="BA:" + tag)

            G_AA, G_BB, G_AB, G_BA = (gA["IC"], gB["IC"], gAB["IC"],
                                      gBA["IC"])
            G_AB_sig = gAB["IC_sigma_engine"]
            det = G_AB * G_AB - G_AA * G_BB
            disc = G_AB * G_AB - G_AA * G_BB
            row = {
                "pair": tag, "G_AA": G_AA, "G_BB": G_BB, "G_AB": G_AB,
                "G_BA": G_BA, "swap_split": G_AB - G_BA,
                "G_AB_sigma_engine": G_AB_sig,
                "engine_split": G_AB - G_AB_sig,
                "det": det,
                "prime_terms_AB": gAB["prime_terms"],
                "prime_terms_AA": gA["prime_terms"],
            }
            if G_BB != 0.0:
                lstar = G_AB / G_BB
                qmin = G_AA - G_AB * G_AB / G_BB
                row["lambda_free"] = lstar
                row["q_min_free"] = qmin
                if disc >= 0:
                    r = math.sqrt(disc)
                    lam_m = (G_AB - r) / G_BB
                    lam_p = (G_AB + r) / G_BB
                    row["roots"] = sorted([lam_m, lam_p])
            rows.append(row)

            # ---- pinned λ from the detector-node interpolation condition
            # span = A − λB realizes −1 at z = ρ + ½:
            #   Â(z) − λB̂(z) = −1  ⟹  λ_pin = (Â(z)+1)/B̂(z)
            # (Laplace of the TEST, not of the pair — direct splines)
            spA = CubicSpline(XG, A)
            spB = CubicSpline(XG, B)
            for rho_im in (14.13472514173497, 40.0):
                z = 1.0 + 1.0j * rho_im        # ρ + ½ with ρ = ½ + iγ
                Av = laplace_spline(spA, z)
                Bv = laplace_spline(spB, z)
                if abs(Bv) < 1e-14:
                    log("  pin: B̂(%s) ~ 0, skip" % str(z))
                    continue
                # committed span coefficients are REAL; the complex target
                # −1 at z is hit in least-squares over real λ, and the
                # residual is reported as the interpolation miss.
                lam_pin = float(((Av + 1.0) * np.conj(Bv)).real
                                / (Bv * np.conj(Bv)).real)
                resid = Av - lam_pin * Bv + 1.0
                q_pin = G_AA - 2 * lam_pin * G_AB + lam_pin ** 2 * G_BB
                # per-prime decomposition of q at λ_pin
                dec = []
                pmapA = {d["n"]: d["term"] for d in row["prime_terms_AA"]}
                pmapAB = {d["n"]: d["term"] for d in row["prime_terms_AB"]}
                alln = sorted(set(pmapA) | set(pmapAB))
                for n in alln:
                    qa = pmapA.get(n, 0.0) - 2 * lam_pin * pmapAB.get(n, 0.0)
                    dec.append({"n": n, "q_term": qa})
                arch_pin = (gA["arch"] + lam_pin ** 2 * gB["arch"]
                            - 2 * lam_pin * gAB["arch"])
                row["pin_%.0f" % rho_im] = {
                    "z": str(z), "lambda": lam_pin, "q": q_pin,
                    "arch_part": arch_pin,
                    "interp_miss_abs": abs(resid),
                    "prime_decomp": dec,
                }
                log("  pin γ=%.1f: λ=%+.6f  q(λ_pin)=%+.6f  miss=%.2e  "
                    "(arch part %+.6f)" % (rho_im, lam_pin, q_pin,
                                           abs(resid), arch_pin))
                log("    q prime decomposition: %s"
                    % ", ".join("n=%d:%+.4f" % (d["n"], d["q_term"])
                                for d in dec))

    # ---- mpmath referee on one arch readout
    if HAVE_MP:
        log("mpmath referee on one pair-test point read")
        mp.mp.dps = 30
        A = heads[1][1]
        B = refs[0][1]
        spA = CubicSpline(XG, A)
        spB = CubicSpline(XG, B)

        def A_f(t):
            return complex(spA(float(t)))

        def B_f(t):
            return complex(spB(float(t)))

        def F_pair_mp(x):
            ts = np.linspace(-LX, LX, 40001)
            acc = mp.mpc(0)
            for k in range(len(ts) - 1):
                tm = 0.5 * (ts[k] + ts[k + 1])
                dt = ts[k + 1] - ts[k]
                acc += mp.mpc(np.conj(A_f(tm)) * B_f(x - tm)) * dt
            return acc

        # midpoint referee on 40001 nodes: sanity-level accuracy only
        x0 = 0.37
        v = F_pair_mp(x0)
        F1 = pair_direct(A, B)
        sp = CubicSpline(XG, F1)
        log("  F(%.2f): mp=%s  grid-spline=%.12f"
            % (x0, mp.nstr(v, 12), complex(sp(x0)).real))

    # ---- summary table
    log("=" * 100)
    log("%-40s %10s %10s %10s %10s %10s %10s"
        % ("pair", "G_AA", "G_BB", "G_AB", "G_BA", "det", "q_min"))
    for r in rows:
        log("%-40s %+10.5f %+10.5f %+10.5f %+10.5f %+10.5f %+10.5f"
            % (r["pair"], r["G_AA"], r["G_BB"], r["G_AB"], r["G_BA"],
               r["det"], r.get("q_min_free", float("nan"))))

    # ---- persist
    os.makedirs("results", exist_ok=True)
    out = {"record": 1798, "grid": {"N": N, "du": DU, "LX": LX},
           "rows": []}
    for r in rows:
        rr = {k: v for k, v in r.items()
              if k not in ("prime_terms_AB", "prime_terms_AA")}
        rr["prime_terms_AB"] = r["prime_terms_AB"]
        rr["prime_terms_AA"] = r["prime_terms_AA"]
        out["rows"].append(rr)
    with open("results/1798_twospan_cross_gate.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    log("results written to results/1798_twospan_cross_gate.json")
    log("DONE")


if __name__ == "__main__":
    main()
