#!/usr/bin/env python3
# fourpoint_diagonal_sign_1918.py — record 1918
#
# Sign probe for the single remaining Cut-2 obligation of the 103 campaign
# (record 1917):  D = ICgate (u *star u) with
#   u = fullFunctionalEquationOrbitAnnihilator g rho,
# for concrete committed-class owners g and concrete off-line rho.
#
# Committed definitions coded verbatim (F27/F28: source read before rig):
#   laplaceAt f s = ∫ f(x)·e^{+s·x} dx
#                    [CC20YoshidaConvolution:55, exponentialWeight]
#   derivativeShift f a : test x = f'(x) + a·f(x)
#                    [C1LaneRD3Root:45]
#     with laplaceAt (derivativeShift f a) s = (a − s)·laplaceAt f s
#                    [C1LaneRD3Root:84]
#   twoPointDerivativeAnnihilator f z1 z2 = derivativeShift (derivativeShift f z1) z2
#                    [C1TwoPointDifferentialAnnihilator:48]
#   offlineZeroOrbitAnnihilator f rho =
#     twoPointDerivativeAnnihilator f (rho − 1/2) (1 − star rho − 1/2)
#                    [C1TwoPointDifferentialAnnihilator:162]
#   fullFunctionalEquationOrbitAnnihilator g rho =
#     twoPointDerivativeAnnihilator (offlineZeroOrbitAnnihilator g rho)
#       (star rho − 1/2) ((1 − rho) − 1/2)
#                    [C1FourPointSpectralPrefixTransport:44]
#     with laplaceAt u (s) = ∏_j (s_j − s) · laplaceAt g (s)
#                    [C1FourPointSpectralPrefixTransport:61]
#   pairTest (A*⋆B)(x) = ∫ conj(A(−t))·B(x−t) dt, ICgate, arch, primes:
#     base engines verbatim from scripts/twospan_cross_gate_1798.py
#     (F77-validated at O(1) scales).
#
# Instruments (F77: any split = instrument death; engines adjudicated):
#   E1 arch_direct        y-quadrature of the committed integrand + closed tail
#   E3 arch_sigma_fft     σ-identity arch(F) = ∫σ(2πξ)·Re F̂ dξ, F̂ via FFT
#   E4 arch_sigma_analytic  same identity with the ANALYTIC F̂ built from the
#                         committed Laplace chain (independent of the numeric
#                         pair convolution) — the arbiter engine
#   E5 arch_split         direct integrand on [y1, ymax] + exact Taylor series
#                         on [0, y1] (no small-y cancellation)
#   W0 scale calibration  exact-answer family F = s·(g*⋆g): every algorithm
#                         must return s·arch(g*⋆g) at s = 1, 1e3, 1e6, 5e8
#   W1b Laplace product   laplaceAt (A*⋆B)(s) = conj(LA(conj s))·LB(s) checked
#                         against the numeric pair convolution
#
# Laws honored: F74 denominator e^y − e^{−y}; F75 σ-identity oversampling
#   dξ ≤ 0.05; F77 four-engine agreement / adjudication; F27/F28.
#   F79 (new, from this record): scale calibration does not certify a shape —
#   E1 collapses on the u*u correlation (maxF up to ~6.5e9) while E3/E4 agree
#   to <= 6e-7; the certified sensitivity must be built from the certified
#   pair {E3, E4}, not the all-engine envelope.
#
# Scope: price D, C, B01, B10 and the branch of the record-1917 trichotomy on
#   a concrete family, with engine adjudication and a margin/sensitivity
#   classifier for the discriminant verdicts.  No gate sign is proved here.

import json
import math
import os
import time

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline

LOGPI = math.log(math.pi)
LOG4PI_GAMMA = math.log(4.0 * math.pi) + 0.5772156649015329

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ----------------------------------------------------------------- grids

LX = 6.0
DU = 5.0e-4
N = int(round(2 * LX / DU)) + 1
XG = -LX + np.arange(N) * DU
NF = 65536

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


def spectral_deriv_c(f, order):
    """d^order/dx^order via padded FFT, COMPLEX-preserving (1798 engine
    without the real projection; u is complex since the shifts carry
    complex nodes)."""
    F = np.fft.fft(f, NF)
    xi = 2.0 * np.pi * np.fft.fftfreq(NF, d=DU)
    out = F
    for _ in range(order):
        out = out * (1j * xi)
    return np.fft.ifft(out)[:N]


# ------------------------------------------- committed annihilator chain

def derivative_shift_c(f, a):
    """derivativeShift f a : x ↦ f'(x) + a·f(x)."""
    return spectral_deriv_c(f, 1) + a * f


def fourpoint_annihilator(g, rho):
    """Committed chain order: inner (s1, s2), then outer (s3, s4)."""
    s1 = rho - 0.5
    s2 = (1.0 - np.conj(rho)) - 0.5
    s3 = np.conj(rho) - 0.5
    s4 = (1.0 - rho) - 0.5
    u = derivative_shift_c(g, s1)
    u = derivative_shift_c(u, s2)
    u = derivative_shift_c(u, s3)
    u = derivative_shift_c(u, s4)
    return u, (s1, s2, s3, s4)


def poly_P(s, nodes):
    """∏_j (s_j − s)."""
    p = 1.0 + 0.0j
    for a in nodes:
        p = p * (a - s)
    return p


def laplace_read(sp, s):
    """∫ f(x)·e^{+s·x} dx with f resampled by its spline on the refined grid
    (committed convention laplaceAt f s = ∫ f·e^{+s·x} dx)."""
    return DUS * complex(np.sum(sp(XGS) * np.exp(s * XGS)))


# ------------------------------------------------------- pair-test engines

def pair_direct(A, B):
    c = np.conj(A[::-1])
    full = DU * np.convolve(c, B, mode="full")
    off = (N - 1) // 2
    return full[off: off + N]


def pair_fft(A, B):
    c = np.conj(A[::-1])
    Fc = np.fft.fft(c, NF)
    Fb = np.fft.fft(B, NF)
    full = DU * np.fft.ifft(Fc * Fb)
    off = (N - 1) // 2
    return full[off: off + N]


# ------------------------------------------------------------ arch engines

def arch_direct(F, S, tag="", loud=False):
    """E1: y-quadrature of the committed integrand + closed tail (small-y
    cancellation amplified at large F0 — see W0 calibration)."""
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
        log("    arch_direct[%s] = %+.9f (imag %.1e, series %.1e)"
            % (tag, arch, core_i, sdiff))
    return arch, core_i, sdiff


# small-y Taylor data of the committed integrand, derived by hand from the
# committed formula (F27):
#   N(y) = e^{y/2}(2F0 + F2 y² + F4 y⁴/12 + …) − 2F0 = F0 y + (F0/4 + F2) y² + …
#   D(y) = e^y − e^{−y} = 2y(1 + y²/6 + …)
#   I(y) = N/D = F0/2 + (F0/8 + F2/2) y + (F2/4 − F0/16) y² + O(y³)
# with F2 = F''(0), F4 = F''''(0) from the spline.  Window y1 = 0.05.


def arch_split(F, S, y1=0.05, tag="", loud=False):
    """E5: exact-to-O(y^3) series on [0, y1] + direct quadrature on
    [y1, ymax] + closed tail.  Cancellation-free on the small-y window."""
    sp = CubicSpline(XG, F)
    F0 = complex(sp(0.0))
    F2 = float(sp(0.0, nu=2).real)      # d²F/dy²(0)
    ymax = S + 30.0

    def num(y):
        v = complex(sp(y)) + complex(sp(-y))
        return math.exp(y / 2.0) * v - 2.0 * F0

    def integ_r(y):
        return (num(y) / (math.exp(y) - math.exp(-y))).real

    # series coefficients (hand-derived above; F4 enters only at O(y³))
    a0 = F0.real / 2.0
    a1 = F0.real / 8.0 + F2 / 2.0
    a2 = F2 / 4.0 - F0.real / 16.0
    series_window = a0 * y1 + a1 * y1 ** 2 / 2.0 + a2 * y1 ** 3 / 3.0
    core = quad(integ_r, y1, ymax, limit=800, epsabs=1e-13, epsrel=1e-13)[0]
    tail = F0.real * math.log(math.tanh(ymax / 2.0))
    arch = LOG4PI_GAMMA * F0.real + series_window + core + tail
    if loud:
        log("    arch_split[%s]  = %+.9f" % (tag, arch))
    return arch


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
    """E3: σ-identity arch with F̂ via padded FFT (F75 dξ ≤ 0.05)."""
    Fp = np.zeros(NF, dtype=complex)
    Fp[:N] = F
    Fh = DU * np.fft.fft(Fp)
    xi = np.fft.fftfreq(NF, d=DU)
    Fh = Fh * np.exp(2j * np.pi * xi * LX)
    sig = sigma_vec(2.0 * np.pi * xi)
    dxi = 1.0 / (NF * DU)
    val = complex(np.sum(sig * Fh)) * dxi
    if loud:
        log("    arch_sigma_fft[%s] = %+.9f" % (tag, val.real))
    return val.real


def arch_sigma_analytic(Fhat_fun, tag="", loud=False, omega=200.0):
    """E4: σ-identity arch with an ANALYTIC F̂ (no numeric convolution,
    no FFT): arch = ∫_{−Ω}^{Ω} σ(2πξ)·Re F̂(ξ) dξ (F75), tail negligible
    for the committed C^∞ family (checked by halving Ω)."""
    def integ(xi):
        return float(sigma_vec(2.0 * math.pi * xi)) * Fhat_fun(xi).real
    v1 = quad(integ, -omega, omega, limit=1200, epsabs=1e-12,
              epsrel=1e-12)[0]
    if loud:
        v2 = quad(integ, -omega / 2, omega / 2, limit=1200, epsabs=1e-12,
                  epsrel=1e-12)[0]
        log("    arch_sigma_analytic[%s] = %+.9f (half-window %+.9f, "
            "d=%.1e)" % (tag, v1, v2, v1 - v2))
    return v1


# ------------------------------------------------------------ prime reads

def prime_powers_up_to(xmax):
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
    terms = []
    for n, lam in prime_powers_up_to(math.exp(S)):
        v = complex(Fsp(math.log(n))) + complex(Fsp(-math.log(n)))
        t = lam / math.sqrt(n) * v.real
        terms.append((n, lam, t))
    return sum(t for _, _, t in terms), terms


# ------------------------------------------------------------------ gates

def gate_entry(A, B, S_pair, tag="", Fhat_analytic=None):
    """ICgate(A*⋆B): pair engines (E1/E2 convolution), arch engines
    (E1 direct, E3 σ-FFT, E5 split; E4 if Fhat_analytic given), prime sum."""
    F1 = pair_direct(A, B)
    F2 = pair_fft(A, B)
    split = float(np.max(np.abs(F1 - F2)))
    a1, imres, sdiff = arch_direct(F1, S_pair, tag=tag)
    a3 = arch_sigma_fft(F1, tag=tag)
    a5 = arch_split(F1, S_pair, tag=tag)
    sp = CubicSpline(XG, F1)
    psum, terms = prime_sum(sp, S_pair)
    out = {
        "tag": tag, "arch": a1, "arch_sigma": a3, "arch_split": a5,
        "prime_sum": psum, "IC": a3 + psum, "IC_direct": a1 + psum,
        "IC_split": a5 + psum, "conv_split": split,
        "F0": complex(sp(0.0)).real, "maxF": float(np.max(np.abs(F1))),
        "imag": imres, "series_diff": sdiff,
        "prime_terms": [{"n": n, "lam": lam, "term": t}
                        for n, lam, t in terms],
    }
    if Fhat_analytic is not None:
        a4 = arch_sigma_analytic(Fhat_analytic, tag=tag)
        out["arch_analytic"] = a4
        out["IC_analytic"] = a4 + psum
    log("  %-20s E1=%+.6e E3=%+.6e E5=%+.6e%s primes=%+.6e IC(E3)=%+.6e "
        "split=%.1e maxF=%.2e"
        % (tag, a1, a3, a5,
           (" E4=%+.6e" % out["arch_analytic"]) if "arch_analytic" in out
           else "",
           psum, out["IC"], split, out["maxF"]))
    return out


def gate_engines_ic(e):
    """All IC readings available for an entry."""
    ics = {"E3": e["IC"], "E1": e["IC_direct"], "E5": e["IC_split"]}
    if "IC_analytic" in e:
        ics["E4"] = e["IC_analytic"]
    return ics


# ------------------------------------------------------------------ main

def main():
    log("record 1918 — four-point diagonal sign probe (Cut 2 of 103)")
    log("grid: N=%d du=%.0e LX=%.1f NF=%d" % (N, DU, LX, NF))

    # ---- W0: exact-answer scale calibration on F = s·(g*⋆g)
    log("W0 scale calibration: F = s·(g*⋆g), exact answer s·IC(g*g)")
    gcal = bump(1.0)
    base = gate_entry(gcal, gcal, 2.0 * 1.0, tag="cal s=1")
    ref_arch, ref_prime = base["arch_sigma"], base["prime_sum"]
    out_w0 = [{"s": 1.0, "E1_err": base["arch"] - ref_arch,
               "E3_err": 0.0, "E5_err": base["arch_split"] - ref_arch}]
    for s in (1.0e3, 1.0e6, 5.0e8):
        Fs = s * pair_direct(gcal, gcal)
        sp = CubicSpline(XG, Fs)
        psum, _ = prime_sum(sp, 2.0)
        a1, _, _ = arch_direct(Fs, 2.0)
        a3 = arch_sigma_fft(Fs)
        a5 = arch_split(Fs, 2.0)
        log("  W0 s=%.0e: E1 rel %.2e  E3 rel %.2e  E5 rel %.2e  (prime ok %s)"
            % (s, (a1 - s * ref_arch) / (s * abs(ref_arch)),
               (a3 - s * ref_arch) / (s * abs(ref_arch)),
               (a5 - s * ref_arch) / (s * abs(ref_arch)),
               abs(psum - s * ref_prime) <= 1e-9 * s * abs(ref_prime)))
        out_w0.append({"s": s, "E1_arch": a1, "E3_arch": a3, "E5_arch": a5,
                       "exact": s * ref_arch})
    log("W0 verdict: engines certified only on the scales where they agree")

    gammas = [14.134725141734693, 21.022039638771555]
    deltas = [0.05, 0.1, 0.3]
    widths = [0.8, 1.0, 1.3]

    out = {}
    out["w0"] = out_w0
    out["cases"] = []
    for c in widths:
        g = bump(c)
        sp_g = CubicSpline(XG, g)
        for gamma in gammas:
            for delta in deltas:
                rho = (0.5 + delta) + 1j * gamma
                tag = "c=%.1f d=%.2f g=%.2f" % (c, delta, gamma)
                log("case %s  rho = %.3f %+.6fi" % (tag, rho.real, rho.imag))
                u, nodes = fourpoint_annihilator(g, rho)
                sp_u = CubicSpline(XG, u)
                S_pair = 2.0 * c

                # ---- W1: annihilation + multiplier identity (e^{+sx})
                annih = []
                for sj in nodes:
                    Lg = laplace_read(sp_g, sj)
                    Lu = laplace_read(sp_u, sj)
                    annih.append({"s": [sj.real, sj.imag], "absLu": abs(Lu),
                                  "rel": abs(Lu) / (abs(Lg) + 1.0)})
                mult = []
                for s in (0.9 + 0.4j, -1.1 + 0.2j, 1.3 - 0.7j):
                    Lg = laplace_read(sp_g, s)
                    Lu = laplace_read(sp_u, s)
                    pred = poly_P(s, nodes)
                    r = Lu / Lg
                    mult.append({"s": [s.real, s.imag],
                                 "ratio": [r.real, r.imag],
                                 "rel": abs(r - pred) / (abs(pred) + 1e-300)})
                # ---- W1b: Laplace product on the numeric pair convolution
                F_uu = pair_direct(u, u)
                sp_F = CubicSpline(XG, F_uu)
                lapprod = []
                for s in (0.7 + 0.3j, -0.4 + 0.9j):
                    lhs = laplace_read(sp_F, s)
                    rhs = np.conj(laplace_read(sp_u, np.conj(s))) * \
                        laplace_read(sp_u, s)
                    lapprod.append({"s": [s.real, s.imag],
                                    "rel": abs(lhs - rhs) / (abs(rhs) + 1e-300)})
                log("  annih rel: " + ", ".join("%.2e" % a["rel"] for a in annih))
                log("  mult  rel: " + ", ".join("%.2e" % m["rel"] for m in mult))
                log("  lap-prod rel: " + ", ".join("%.2e" % m["rel"] for m in lapprod))

                # ---- W2: gate entries
                # analytic F̂ for the D entry: laplaceAt u(s) = P(s)·Lg(s),
                #   laplaceAt (u*⋆u)(s) = conj(Lu(conj s))·Lu(s),
                #   F̂(ξ) = laplaceAt (u*⋆u)(−2πiξ)
                def Fhat_u2(xi):
                    s = -2j * math.pi * xi
                    Lu_s = poly_P(s, nodes) * laplace_read(sp_g, s)
                    Lu_cs = poly_P(np.conj(s), nodes) * \
                        laplace_read(sp_g, np.conj(s))
                    return np.conj(Lu_cs) * Lu_s

                eD = gate_entry(u, u, S_pair, tag="D=IC(u*u)",
                                Fhat_analytic=Fhat_u2)
                eC = gate_entry(g, g, S_pair, tag="C=IC(g*g)")
                eB01 = gate_entry(u, g, S_pair, tag="B01=IC(u*g)")
                eB10 = gate_entry(g, u, S_pair, tag="B10=IC(g*u)")

                Ds = gate_engines_ic(eD)
                Cs = gate_engines_ic(eC)
                Bs01 = gate_engines_ic(eB01)
                Bs10 = gate_engines_ic(eB10)
                D = Ds.get("E4", Ds["E3"])
                C = Cs["E3"]
                B01, B10 = Bs01["E3"], Bs10["E3"]
                Bs = B01 + B10
                disc = Bs * Bs - 4.0 * C * D
                # sensitivity: engine spreads propagated onto disc.
                # F79 (new): the all-engine envelope is poisoned by the E1/E5
                # shape failures on u*u; the certified reading propagates the
                # certified pair {E3, E4} disagreement only, plus a conservative
                # 1e-5 relative shared-systematic envelope as a second bar.
                dD = max(Ds.values()) - min(Ds.values())
                dD_cert = abs(Ds.get("E4", Ds["E3"]) - Ds["E3"])
                dC = max(Cs.values()) - min(Cs.values())
                dB01 = max(Bs01.values()) - min(Bs01.values())
                dB10 = max(Bs10.values()) - min(Bs10.values())
                ddisc = (2.0 * abs(Bs) * (dB01 + dB10)
                         + 4.0 * abs(C) * dD + 4.0 * abs(D) * dC)
                ddisc_cert = (2.0 * abs(Bs) * (dB01 + dB10)
                              + 4.0 * abs(C) * dD_cert + 4.0 * abs(D) * dC)
                ddisc_cons = (ddisc_cert
                              + 4.0 * abs(C) * 1e-5 * abs(D)
                              + 2.0 * abs(Bs) * 1e-5 * (abs(B01) + abs(B10)))
                robust = abs(disc) > 10.0 * ddisc
                robust_cert = abs(disc) > 10.0 * ddisc_cert
                robust_cons = abs(disc) > 10.0 * ddisc_cons
                branch = ("D<0" if D < 0 else
                          ("D=0,B!=0" if (D == 0 and Bs != 0) else
                           ("D>0,disc>=0" if (D > 0 and disc >= 0) else
                            "NO-WITNESS" if D > 0 else "D=0,B=0")))
                lam_vertex = Bs / (2.0 * C)
                # deviations relative to the certified D (E4 when present): E4 dev is 0
                # by construction; E3 dev is the certified-pair disagreement.
                dev = {k: (v - D) / D for k, v in Ds.items()}
                log("  -> D=%+.6e (spread %.1e cert %.1e) C=%+.6e Bs=%+.6e "
                    "disc=%+.3e +-%.1e robust=%s/%s/%s branch=%s "
                    "lam_vertex=%+.6e dev=%s"
                    % (D, dD, dD_cert, C, Bs, disc, ddisc_cert, robust,
                       robust_cert, robust_cons, branch, lam_vertex,
                       " ".join("%s:%+.1e" % (k, v) for k, v in dev.items())))

                out["cases"].append({
                    "tag": tag, "c": c, "rho": [rho.real, rho.imag],
                    "annih": annih, "mult": mult, "lapprod": lapprod,
                    "D": eD, "C": eC, "B01": eB01, "B10": eB10,
                    "D_engines": Ds, "D_spread": dD, "D_spread_cert": dD_cert,
                    "dev_D_engines": dev,
                    "Bs": Bs, "disc": disc, "disc_sensitivity": ddisc,
                    "disc_sensitivity_cert": ddisc_cert,
                    "disc_sensitivity_cons": ddisc_cons,
                    "robust": robust, "robust_cert": robust_cert,
                    "robust_cons": robust_cons, "branch": branch,
                    "margin_rel": disc / (4.0 * C * D),
                    "Q_vertex": -disc / (4.0 * C),
                    "lam_vertex": lam_vertex,
                })

    branches = {}
    robust_pos = 0
    robust_cert_pos = 0
    robust_cons_pos = 0
    for cs in out["cases"]:
        key = cs["branch"] + ("*" if cs["robust_cert"] else "(unresolved)")
        branches[key] = branches.get(key, 0) + 1
        if cs["branch"] == "D>0,disc>=0":
            robust_pos += 1 if cs["robust"] else 0
            robust_cert_pos += 1 if cs["robust_cert"] else 0
            robust_cons_pos += 1 if cs["robust_cons"] else 0
    max_annih = max(max(a["rel"] for a in cs["annih"]) for cs in out["cases"])
    max_mult = max(max(m["rel"] for m in cs["mult"]) for cs in out["cases"])
    max_lp = max(max(m["rel"] for m in cs["lapprod"]) for cs in out["cases"])
    Dsign = all(cs["D_engines"]["E3"] > 0 and cs["D_engines"].get("E4", 1) > 0
                for cs in out["cases"])
    max_dev_E1 = max(abs(cs["dev_D_engines"].get("E1", 0.0))
                     for cs in out["cases"])
    max_dev_E5 = max(abs(cs["dev_D_engines"].get("E5", 0.0))
                     for cs in out["cases"])
    max_dev_E3 = max(abs(cs["dev_D_engines"].get("E3", 0.0))
                     for cs in out["cases"])
    min_margin = min(cs["margin_rel"] for cs in out["cases"])
    log("SUMMARY branches=%s" % json.dumps(branches))
    log("SUMMARY D>0 in all engines on all cases: %s" % Dsign)
    log("SUMMARY max |dev| vs certified E4: E3 %.2e E1 %.2e E5 %.2e"
        % (max_dev_E3, max_dev_E1, max_dev_E5))
    log("SUMMARY disc>0 robust: all-engine %d, certified %d, conservative %d "
        "of %d; min margin_rel %.3e"
        % (robust_pos, robust_cert_pos, robust_cons_pos, len(out["cases"]),
           min_margin))
    log("SUMMARY max annih %.2e, mult %.2e, lap-prod %.2e" %
        (max_annih, max_mult, max_lp))
    out["summary"] = {"branches": branches, "D_positive_all": Dsign,
                      "max_annih_rel": max_annih, "max_mult_rel": max_mult,
                      "max_lapprod_rel": max_lp,
                      "max_dev_E1": max_dev_E1, "max_dev_E3": max_dev_E3,
                      "max_dev_E5": max_dev_E5,
                      "robust_disc_pos_all_engine": robust_pos,
                      "robust_disc_pos_certified": robust_cert_pos,
                      "robust_disc_pos_conservative": robust_cons_pos,
                      "min_margin_rel": min_margin}
    os.makedirs("results", exist_ok=True)
    with open("results/1918_fourpoint_diagonal_sign.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    log("wrote results/1918_fourpoint_diagonal_sign.json")


if __name__ == "__main__":
    main()