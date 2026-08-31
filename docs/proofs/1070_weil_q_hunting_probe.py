# 1070 - LEVEL-1 Weil-functional hunting probe (closed form, mpmath).
#
# Design record: 1070_weil_q_hunting_level1.md (fork stated BEFORE the run).
# Pinned formulas: weil-compo.tex labels mellin / bombieriexplicit / 1 / 2 /
# sch22 / vanishing / mainprop (see record s1 table).
#
# Family:  g~_d(s) = N(d) * V_F(s) * exp(d^2 s^2 / 2),  V_F = s(s-1)(s^2-1/4)
#          f~(s)  = g~_d(s+1) g~_d(s-1) = N^2 V_F(s+1) V_F(s-1) exp(d^2(s^2+1))
#          N(d) normalizes max_t |g~_d(1/2+it)| = 1.
# Measured: margin(d) = sum 2 Re f~(1/2+i g_j) (+ tail bound);
#           P_j = 2 Re f~(1/2+i g_j);
#           A_j(beta) = 2 Re[f~(beta+i g_j) + f~(1-beta+i g_j)];
#           flip_j(d) = min_beta [margin + A_j - P_j]  (< 0 => family flips).
# ANCHOR (must pass first): CC20's own example test f~(s)=(1-4s^2)^2 e^{s^2/2}
# closes the explicit formula identity (zero + archimedean + prime sides).
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with mpmath python -u \
#      docs/proofs/1070_weil_q_hunting_probe.py > /home/peter/1070_probe.log 2>&1; \
#      echo DONE-RC=$?'
# Env: JLIST_1070, OCTAVES_1070, BETA_1070, CACHE_GAMMA_MAX_1070

import json
import os

import numpy as np
from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, sqrt as msqrt, \
    zetazero, quad as mquad

mp.dps = 30

JLIST = json.loads(os.environ.get("JLIST_1070", "[1, 2, 3, 5, 10, 20, 30]"))
OCTAVES = int(os.environ.get("OCTAVES_1070", "3"))          # delta range depth
BETAS = json.loads(os.environ.get("BETA_1070",
                                  "[0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.45]"))
CACHE_GMAX = float(os.environ.get("CACHE_GMAX_1070", "0"))  # 0 => auto

EULER = mpf("0.57721566490153286060651209008240243104215933593992")


def vf(s):
    """V_F(s) = s (s-1) (s^2 - 1/4), mpmath complex."""
    return s * (s - 1) * (s * s - mpf(1) / 4)


def make_ftilde(delta, norm):
    """f~(s) for the conformant family, as a callable."""
    n2 = norm * norm
    d2 = delta * delta

    def ftil(s):
        return n2 * vf(s + 1) * vf(s - 1) * mexp(d2 * (s * s + 1))
    return ftil


def normalize_family(delta):
    """N(delta): max_t |V_F(1/2+it)| e^{d^2(1/4-t^2)/2} -> 1 (float64 search)."""
    ts = np.linspace(1e-9, 8.0 / delta, 60000)
    # |V_F(1/2+it)| = (1/4+t^2) * t * sqrt(1+t^2)
    vabs = (0.25 + ts * ts) * ts * np.sqrt(1.0 + ts * ts)
    shape = vabs * np.exp(delta * delta * (0.25 - ts * ts) / 2.0)
    tstar = float(ts[int(np.argmax(shape))])
    peak = vf(mpf(1) / 2 + 1j * mpf(repr(tstar)))
    m = abs(peak) * mexp(delta * delta * (mpf(1) / 4 - mpf(repr(tstar)) ** 2) / 2)
    norm = 1 / m
    return norm, tstar


def zero_cache(gmax):
    """Ordinates gamma_j up to gmax (mpmath, cached once)."""
    gam = []
    j = 0
    while True:
        j += 1
        g = mp.im(zetazero(j))
        if g > gmax:
            break
        gam.append(g)
        if j % 250 == 0:
            print(f"[cache] j={j} gamma={float(g):.1f} / gmax={gmax:.1f}", flush=True)
    print(f"[cache] done: {j - 1} zeros up to gamma {gmax:.1f}", flush=True)
    return gam


def ftil_online_row(ftil, gam):
    """2 Re f~(1/2+i g) for each cached zero (list, mpmath)."""
    return [2 * mp.re(ftil(mpf(1) / 2 + 1j * g)) for g in gam]


def tail_bound(delta, norm, cutoff):
    """Upper bound of 2 sum_{gamma>cutoff} |Re f~| via density x integral."""
    d2, n2 = delta * delta, norm * norm

    def mag(t):
        s = mpf(1) / 2 + 1j * mpf(repr(t))
        return float(abs(n2 * vf(s + 1) * vf(s - 1) * mexp(d2 * (s * s + 1))))
    ts = np.linspace(cutoff, cutoff + 8.0 / delta, 4000)
    dens = np.log(ts / (2 * np.pi)) / (2 * np.pi)
    mags = np.array([mag(t) for t in (cutoff, cutoff + 4.0 / delta)])
    scale = float(mags.max()) + 1e-300
    # conservative: density-integral x max |f~| on the tail window
    return 2 * float(np.trapezoid(dens, ts)) * scale


def anchor_gate():
    """Explicit-formula identity on CC20's own example test (record s3)."""
    print("=== ANCHOR: CC20 example test f~(s) = (1-4s^2)^2 e^{s^2/2} ===", flush=True)

    def G(u):
        u = mpf(repr(u)) if isinstance(u, float) else u
        return msqrt(2 * mpi) * (16 * u**4 - 104 * u**2 + 57) * mexp(-u * u / 2)

    # sub-gate: numerical inverse Fourier at sample points
    def fhat(t):
        t = mpf(repr(t)) if isinstance(t, float) else t
        return (1 + 4 * t * t) ** 2 * mexp(-t * t / 2)
    for u0 in (0.0, 0.5, 1.3):
        num = mquad(lambda tt: fhat(tt) * mexp(1j * tt * u0), [-40, 0, 40]) / (2 * mpi)
        err = abs(num - G(u0))
        print(f"ANCHOR|invfourier|u={u0}|G={float(G(u0)):.6f}"
              f"|num={float(num):.6f}|err={float(err):.2e}")
        assert err < 1e-9, "inverse Fourier sub-gate failed"

    triv = 18 * msqrt(mpf(1) * mp.e)
    lhs_f = lambda s: (1 - 4 * s * s) ** 2 * mexp(s * s / 2)
    zeros_side = mpf(0)
    for j in range(1, 21):
        g = mp.im(zetazero(j))
        zeros_side += 2 * mp.re(lhs_f(mpf(1) / 2 + 1j * g))
    tb = abs(lhs_f(mpf(1) / 2 + 1j * mpf(78))) * 400  # density(78)~0.66, e^{-2900} tail
    print(f"ANCHOR|zeros_side={float(zeros_side):.6e}|tail<{float(tb):.1e}")

    # archimedean side (bombieriexplicit2 in the u coordinate)
    def integrand(u):
        return (G(u) + mexp(-u) * G(-u) - 2 * mexp(-u) * G(mpf(0))) / (1 - mexp(-2 * u))
    archi = (mlog(4 * mpi) + EULER) * G(mpf(0)) + \
        mquad(integrand, [mpf("1e-12"), mpf("0.01"), 1, 10, 40])
    print(f"ANCHOR|W_R={float(archi):.8f}")

    # prime side
    PMAX, MMAX = 1000000, 40
    sieve = np.ones(PMAX + 1, dtype=bool)
    sieve[:2] = False
    for n0 in range(2, int(PMAX ** 0.5) + 1):
        if sieve[n0]:
            sieve[n0 * n0:: n0] = False
    primes = np.nonzero(sieve)[0]
    prime_side = mpf(0)
    for p0 in primes:
        lp = mlog(mpf(int(p0)))
        for m0 in range(1, MMAX + 1):
            u0 = m0 * lp
            term = G(u0) + mexp(-u0) * G(-u0)
            prime_side += lp * term
            if abs(term) * lp < mpf("1e-40"):
                break
    print(f"ANCHOR|prime_side={float(prime_side):.8f}|pmax={PMAX}")

    rhs = triv - archi - prime_side
    resid = abs(zeros_side - rhs) / abs(triv)
    print(f"ANCHOR|trivial={float(triv):.8f}|rhs={float(rhs):.8e}"
          f"|RESID={float(resid):.3e}  (gate <= 1e-6)")
    assert resid < 1e-6, "ANCHOR GATE FAILED: normalization chain broken"
    assert abs(zeros_side - rhs) < mpf("1e-20"), \
        "ANCHOR absolute closure failed (all sides should be ~1e-36)"
    print("ANCHOR|GATE-PASS", flush=True)


def run():
    print("=== 1070 LEVEL-1 Weil hunting probe (closed form) ===", flush=True)
    anchor_gate()

    # global zero cache size from the smallest delta in the scan
    g30 = float(mp.im(zetazero(30)))
    d_min = (1.177 / g30) / (2.0 ** (OCTAVES / 2))
    gmax = CACHE_GMAX if CACHE_GMAX > 0 else 6.0 / d_min
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])

    print("\n=== FORK SCAN (flips: margin + A - P < 0) ===", flush=True)
    for j in JLIST:
        gj = mp.im(zetazero(int(j)))
        gamma_j = float(gj)
        d_peak = 2.0 / gamma_j                      # V_F polynomial-peak tuning
        d_coarse = 1.177 / gamma_j                  # w >= 1/2 symbol tuning (1069)
        d_grid = [d_peak, d_coarse]
        d = d_coarse
        for _ in range(2 * OCTAVES):
            d = d / (2.0 ** 0.5)
            d_grid.append(d)
        best = (float("inf"), 0.0, 0.0)
        for delta in d_grid:
            norm, tstar = normalize_family(delta)
            ftil = make_ftilde(delta, norm)
            cutoff = max(6.0 / delta, 3.0 * gamma_j)
            ncov = int(np.searchsorted(gam_np, cutoff))
            tb = tail_bound(delta, norm, gam_np[ncov - 1] if ncov else 0.0)
            rows = ftil_online_row(ftil, gam[:ncov])
            margin = sum(rows)                      # trivial side = 0 exactly
            Pj = rows[j - 1]
            flips = []
            for b in BETAS:
                bb = mpf(repr(b))
                A = 2 * (mp.re(ftil(bb + 1j * gj)) + mp.re(ftil(1 - bb + 1j * gj)))
                flips.append(float(margin + A - Pj))
            imin = int(np.argmin(flips))
            fl = flips[imin]
            tag = "FLIP" if fl < 0 else "ok"
            print(f"FORK|j={j}|gamma={gamma_j:.3f}|delta={delta:.5f}"
                  f"|tpeak={tstar:.2f}|margin={float(margin):.5f}"
                  f"|P={float(Pj):.5f}|minA-P={fl:.5f}@beta={BETAS[imin]}"
                  f"|ratio={fl / float(margin) if margin != 0 else float('nan'):.4f}"
                  f"|tail<{tb:.1e}|{tag}", flush=True)
            if fl < best[0]:
                best = (fl, delta, BETAS[imin])
        print(f"VERDICT-ROW|j={j}|gamma={gamma_j:.2f}|best_flip={best[0]:.5f}"
              f"|at_delta={best[1]:.5f}|at_beta={best[2]}"
              f"|{'HUNTS' if best[0] < 0 else 'NO-FLIP'}", flush=True)

    # symmetry sub-gate (j=1, coarse delta)
    g1 = mp.im(zetazero(1))
    dcoarse = 1.177 / float(g1)
    norm, _ = normalize_family(dcoarse)
    ftil = make_ftilde(dcoarse, norm)
    b = mpf("0.1")
    A1 = 2 * (mp.re(ftil(b + 1j * g1)) + mp.re(ftil(1 - b + 1j * g1)))
    A2 = 2 * (mp.re(ftil(1 - b + 1j * g1)) + mp.re(ftil(b + 1j * g1)))
    sym = abs(A1 - A2) / max(abs(A1), mpf("1e-300"))
    print(f"\nGATE|A-symmetry|rel={float(sym):.1e} (<= 1e-10)")
    assert sym < 1e-10, "A(beta) != A(1-beta)"
    print("=== done: grep 'ANCHOR|FORK|VERDICT-ROW|GATE' for the fork table ===")


if __name__ == "__main__":
    run()
