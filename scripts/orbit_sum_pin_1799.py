#!/usr/bin/env python3
# orbit_sum_pin_1799.py — record 1799 (v2: modulated basis)
#
# The real orbit-sum pin: instantiate the committed interpolation system of
# OrbitG8Geometry on a finite family and read the gate at the pinned test.
#
# Committed structure coded (F27/F28):
#   T  = (base^{⋆(n+1)}) ⋆ correction          [convolutionIterate + convolution]
#   g  = halfDensityShift(T) = e^{x/2}·T(x)     [halfDensityShift_apply]
#   L[halfDensityShift f](s) = L[f](s + 1/2)    [laplaceAt_halfDensityShift]
#   laplaceAt uses the +s convention: L[f](s) = ∫ f(x) e^{+sx} dx
#   square Laplace pairing: L[g*⋆g](u) = conj(L[g](−ū))·L[g](u)
#
# Interpolation system (healthyUnscaledTargetNodes / Value):
#   orbit {ρ, 1−ρ̄, ρ̄, 1−ρ}: T̂ = 1, −1, 0, 0 ;  detector ρ+½: T̂ = −1
#   centered orbit sum: Σ_{v ∈ {u,−ū,ū,−u}} L[g²](v) = −2, u = ρ−½
#
# v2 instrument law (E-E): a static-width basis is NUMERICALLY SINGULAR at
# height γ (cond 1.4e17, α ~ 1e20 — first run). Interpolation at s = β+iγ
# demands frequency-γ oscillation: basis φ_j(x)·e^{−iγx} (live rows) and
# φ_j(x)·e^{+iγx} (dead rows), block-solvable; the off-block contamination
# is the physical decay e^{−cγw}.  Base width scales as c/γ (same law).
#
# Gate read: ICgate(g*⋆g), arch by the 1741 σ-identity engine (oscillation-
# immune) + direct y-quadrature cross-check; primes by the committed term.
# Scope: dyadic ball zero-control and tail budget NOT instantiated.

import json
import math
import os
import time

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline

LOGPI = math.log(math.pi)
LOG2 = math.log(2.0)
LOG4PI_GAMMA = math.log(4.0 * math.pi) + 0.5772156649015329

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


LX = 8.0
DU = 5.0e-4
N = int(round(2 * LX / DU)) + 1
XG = -LX + np.arange(N) * DU
NF = 131072


def bump(c, center=0.0):
    f = np.zeros_like(XG)
    m = np.abs(XG - center) < c
    xm = (XG[m] - center) / c
    f[m] = np.exp(-1.0 / (1.0 - xm * xm))
    return f


def l2_normalize(f):
    return f / math.sqrt(DU * float(np.sum(np.abs(f) ** 2)))


def spectral_root(h, coeffs):
    F = np.fft.fft(h, NF)
    xi = 2.0 * np.pi * np.fft.fftfreq(NF, d=DU)
    for a in coeffs:
        F = F * (1j * xi - a)
    g = np.fft.ifft(F)[:N]
    return np.real(g) if np.max(np.abs(np.imag(g))) < 1e-9 else g


def laplace_plus(sp, s):
    return DUS * complex(np.sum(sp(XGS) * np.exp(s * XGS)))


DUS = 1.0e-4
NS = int(round(2 * LX / DUS)) + 1
XGS = -LX + np.arange(NS) * DUS


def conv_off(a, b):
    ca = a if np.iscomplexobj(a) else a.astype(complex)
    cb = b if np.iscomplexobj(b) else b.astype(complex)
    full = DU * np.fft.ifft(np.fft.fft(ca, NF) * np.fft.fft(cb, NF))
    off = (N - 1) // 2
    return full[off: off + N]


# ------------------------------------------------- sigma engine (1741)

def psi_asym(z, M=7):
    w = 1.0 / (z * z)
    coeffs = [1.0 / 12.0, -1.0 / 120.0, 1.0 / 252.0, -1.0 / 240.0,
              1.0 / 132.0, -691.0 / 32760.0, 1.0 / 12.0]
    s = sum(coeffs[k] * w ** (k + 1) for k in range(M))
    return np.log(z) - 0.5 / z - s


def sigma_vec(om):
    z = 0.25 - 0.5j * np.asarray(om, dtype=complex)
    return LOGPI - psi_asym(z).real


def arch_sigma(F):
    Fp = np.zeros(NF, dtype=complex)
    Fp[:N] = F
    Fh = DU * np.fft.fft(Fp)
    xi = 2.0 * np.pi * np.fft.fftfreq(NF, d=DU)
    Fh = Fh * np.exp(2j * np.pi * xi * LX)      # grid offset phase
    dxi = 2.0 * np.pi / (NF * DU)
    om = 2.0 * np.pi * xi
    return complex(np.sum(sigma_vec(om) * Fh) * dxi).real


def arch_direct(F, S):
    sp = CubicSpline(XG, F)
    F0 = complex(sp(0.0))
    ymax = S + 30.0

    def integ(y):
        v = complex(sp(y)) + complex(sp(-y))
        return ((math.exp(y / 2.0) * v - 2.0 * F0)
                / (math.exp(y) - math.exp(-y))).real

    core = quad(integ, 1e-8, ymax, limit=2000, epsabs=1e-12,
                epsrel=1e-12)[0]
    tail = F0.real * math.log(math.tanh(ymax / 2.0))
    return LOG4PI_GAMMA * F0.real + core + tail


def prime_sum(sp, S):
    n_max = int(math.floor(math.exp(S)))
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n_max ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    total = 0.0
    terms = {}
    for p in range(2, n_max + 1):
        if sieve[p]:
            pk = p
            while pk <= n_max:
                v = complex(sp(math.log(pk))) + complex(sp(-math.log(pk)))
                t = math.log(p) / math.sqrt(pk) * v.real
                total += t
                terms[pk] = t
                pk *= p
    return total, terms


# ------------------------------------------------------------ the system

def build_case(beta, gamma, cb, k):
    wb = cb / gamma
    # base with EXACT zeros at {1/2, 1, 3/2}: bump combination whose Laplace
    # = L[phi_w](s) * sum_j c_j e^{s mu_j}; the 3x4 nullspace fixes the c_j.
    mu = np.array([-0.45, -0.15, 0.15, 0.45])
    A = np.array([[math.exp(m * s) for m in mu] for s in (0.5, 1.0, 1.5)])
    cvec = np.linalg.svd(A)[2][-1]
    zerofac = max(abs(A @ cvec))
    base = sum(cvec[j] * bump(wb, mu[j]) for j in range(4))
    base = base / math.sqrt(DU * float(np.sum(base ** 2)))

    def lap_grid(f, s):
        return DU * complex(np.sum(f * np.exp(s * XG)))

    nodes = [complex(beta, gamma), complex(1.0 - beta, gamma),
             complex(beta, -gamma), complex(1.0 - beta, -gamma),
             complex(beta + 0.5, gamma)]
    targets = [1.0, -1.0, 0.0, 0.0, -1.0]
    bhk = [lap_grid(base, s) ** k for s in nodes]

    mod = np.exp(-1j * gamma * XG)
    basis = [l2_normalize(bump(w, c)) * mod
             for (w, c) in [(0.35, -0.2), (0.35, 0.2), (0.5, 0.0)]]           + [l2_normalize(bump(w, c)) / mod
             for (w, c) in [(0.3, -0.15), (0.3, 0.15)]]
    M = np.array([[lap_grid(ph, s) for ph in basis] for s in nodes])
    rhs = np.array([t / b for t, b in zip(targets, bhk)])
    cond = float(np.linalg.cond(M))
    al = np.linalg.solve(M, rhs)
    corr = sum(al[j] * basis[j] for j in range(5))

    T = corr
    for _ in range(k):
        T = conv_off(base, T)
    resid = max(abs(lap_grid(T, s) - t) for t, s in zip(targets, nodes))

    u = complex(beta - 0.5, gamma)
    vs = [u, -np.conj(u), np.conj(u), -u]
    g = np.exp(XG / 2.0) * T
    gh = {v: lap_grid(g, v) for v in set(vs) | {-np.conj(v) for v in vs}}
    orbit_sum = complex(sum(np.conj(gh[-np.conj(v)]) * gh[v] for v in vs))

    F = conv_off(np.conj(g[::-1]), g)
    S_cap = min(2.0 * (k * wb + 0.85), LX - 0.5)
    arch_s = arch_sigma(F)
    arch_d = arch_direct(F, S_cap)
    fsp = CubicSpline(XG, F)
    psum, terms = prime_sum(fsp, S_cap)
    gate = arch_s + psum
    return {
        "beta": beta, "gamma": gamma, "cb": cb, "k": k, "wb": wb,
        "cond": cond, "zerofac": zerofac,
        "max_alpha": float(np.max(np.abs(al))),
        "interp_resid": float(resid), "orbit_sum": orbit_sum,
        "norm_g2": DU * float(np.sum(np.abs(F) ** 2)) ** 0.5,
        "arch_sigma": arch_s, "arch_direct": arch_d,
        "arch_gap": abs(arch_s - arch_d),
        "prime_sum": psum, "gate": gate,
        "terms": {str(a): b for a, b in terms.items()},
    }


def main():
    log("record 1799 v3 — orbit-sum pin: constructed-zero base + modulated basis")
    log("grid N=%d du=%.0e LX=%.1f NF=%d" % (N, DU, LX, NF))
    results = []
    for beta in (0.55, 0.6):
        for gamma in (14.13472514173497, 40.0):
            for cb in (0.6, 1.2):
                for k in (1, 2):
                    r = build_case(beta, gamma, cb, k)
                    log("β=%.4f γ=%5.1f cb=%.1f k=%d | cond=%.1e "
                        "α|max=%.1e resid=%.1e orbSum=%+.4f%+.4fi "
                        "gap(σ,direct)=%.1e gate=%+.5f "
                        "(archσ %+.5f + primes %+.5f)"
                        % (beta, gamma, cb, k, r["cond"],
                           r["max_alpha"], r["interp_resid"],
                           r["orbit_sum"].real, r["orbit_sum"].imag,
                           r["arch_gap"], r["gate"], r["arch_sigma"],
                           r["prime_sum"]))
                    results.append(r)

    log("=" * 100)
    ok = [r for r in results
          if r["interp_resid"] < 1e-6 and abs(r["orbit_sum"] + 2) < 1e-4
          and r["arch_gap"] < 1e-4]
    log("admissible (resid<1e-6, orbSum=−2, engines agree<1e-4): %d/%d"
        % (len(ok), len(results)))
    for r in ok:
        log("  β=%.6f γ=%5.1f cb=%.1f k=%d gate=%+.5f %s"
            % (r["beta"], r["gamma"], r["cb"], r["k"], r["gate"],
               "NEG" if r["gate"] < 0 else "POS"))
    neg = [r for r in ok if r["gate"] < 0]
    log("VERDICT: %d/%d admissible builds read gate <= 0"
        % (len(neg), len(ok)))

    os.makedirs("results", exist_ok=True)
    def flat(r):
        d = {}
        for kk, vv in r.items():
            if kk == "terms":
                continue
            if isinstance(vv, complex):
                d[kk + "_re"] = vv.real
                d[kk + "_im"] = vv.imag
            else:
                d[kk] = vv
        return d
    out = {"record": 1799, "grid": {"N": N, "du": DU, "LX": LX},
           "cases": [flat(r) for r in results]}
    with open("results/1799_orbit_sum_pin.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    log("results → results/1799_orbit_sum_pin.json")


def scan():
    """Law W2 probe: gate vs zero height at fixed (beta, cb, k)."""
    log("gamma-scan: beta=0.55 cb=0.6 k=1")
    print("%6s %12s %12s %12s %14s"
          % ("gamma", "gate", "arch_sig", "primes", "prime2cell"))
    rows = []
    for gamma in np.arange(14.0, 40.01, 1.0):
        r = build_case(0.55, float(gamma), 0.6, 1)
        p2 = r["terms"].get("2", float("nan"))
        print("%6.1f %12.4e %12.4f %12.4e %14.4e"
              % (gamma, r["gate"], r["arch_sigma"], r["prime_sum"], p2))
        rows.append((gamma, r["gate"], p2))
    g = np.array([x[0] for x in rows])
    p = np.array([x[1] for x in rows])
    flips = [round(g[i], 1) for i in range(1, len(g))
             if (p[i] > 0) != (p[i - 1] > 0)]
    log("gate sign flips at gamma: %s" % flips)
    A2 = np.c_[np.cos(2 * g * LOG2), np.sin(2 * g * LOG2), np.ones_like(g)]
    coef = np.linalg.lstsq(A2, p, rcond=None)[0]
    pred = A2 @ coef
    amp = math.hypot(coef[0], coef[1])
    log("single-phase cos(2gamma log2) fit: amp=%.3e max|resid|/amp=%.2f "
        "(multi-frequency beats if >> 1)"
        % (amp, np.max(np.abs(pred - p)) / amp))


if __name__ == "__main__":
    import sys
    if "--scan" in sys.argv:
        scan()
    else:
        main()
