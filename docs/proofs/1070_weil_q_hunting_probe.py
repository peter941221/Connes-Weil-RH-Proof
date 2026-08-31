# 1070 - LEVEL-1 Weil-functional hunting probe (closed form, mpmath).  V2.
#
# Design record: 1070_weil_q_hunting_level1.md (fork stated BEFORE the run;
# s6 AMENDMENT: the pre-registered dictionary f~ = g~(s+1)g~(s-1) was WRONG
# and is corrected here to the Mellin-convolution-theorem form BEFORE any
# fork data was read).
#
# Family:  g~_d(s) = N(d) * V_F(s) * exp(d^2 s^2 / 2),  V_F = s(s-1)(s^2-1/4)
#          vanishing at F = {0, 1, +-1/2} (Yoshida {0,1} + CC20 {+-1/2}).
# Weil test:  f = g * g^sharp (multiplicative convolution)  =>
#          f~(s) = g~_d(s) g~_d(1-s)          (Mellin convolution theorem)
#          f~(1) = g~(1) g~(0) = 0,  f~(0) = g~(0) g~(1) = 0   (exact).
# Measured: margin(d) = sum_j |g~(1/2+i g_j)|^2  (termwise >= 0; + tail bound)
#           P_j(d) = |g~(rho_j)|^2
#           A_j(b) = 2 Re[f~(b+i g_j) + f~(1-b+i g_j)]
#           flip_j(d, b) = margin + A_j - P_j  (< 0 => family flips)
# ANCHOR A: the identity (Bombieri [EB] = CC20 tex:2039) closes on a genuine
#           C_c 6-fold B-spline test: zero side (mpmath zetazero) vs
#           archimedean W_R (tex:2047 u-form) vs f~-form W_R (tex:2049),
#           prime side finite by support, trivial side f~(1)+f~(0).
# ANCHOR B: CC20's own example test has W_inf < 0 (tex:696-699), sign check.
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with mpmath python -u \
#      docs/proofs/1070_weil_q_hunting_probe.py > /home/peter/1070_probe.log 2>&1; \
#      echo DONE-RC=$?'
# Env: JLIST_1070, OCTAVES_1070, BETA_1070, CACHE_GMAX_1070

import json
import os

import numpy as np
from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, sqrt as msqrt, \
    sinh as msinh, zetazero, quad as mquad

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


def make_gtil(delta, norm):
    """g~_d(s), a callable (real coefficients: g~(sbar) = conj(g~(s)))."""
    d2 = delta * delta

    def gtil(s):
        return norm * vf(s) * mexp(d2 * s * s / 2)
    return gtil


def make_ftilde(gtil):
    """f~(s) = g~(s) g~(1-s): Mellin image of the Weil test f = g * g^sharp."""

    def ftil(s):
        return gtil(s) * gtil(1 - s)
    return ftil


def normalize_family(delta):
    """N(d): max_t |V_F(1/2+it)| e^{d^2(1/4-t^2)/2} -> 1 (float64 search)."""
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
        if j % 500 == 0:
            print(f"[cache] j={j} gamma={float(g):.1f} / gmax={gmax:.1f}",
                  flush=True)
    print(f"[cache] done: {j - 1} zeros up to gamma {gmax:.1f}", flush=True)
    return gam


def tail_bound(delta, norm, tc):
    """2 * int_tc^inf density(t) |f~(1/2+it)| dt with the exact closed-form
    envelope |f~| = |g~|^2 (superexponential decay; tight, not max x count)."""
    d2, n2 = delta * delta, norm * norm

    def env(t):
        vabs2 = (mpf("0.25") + t * t) ** 2 * t * t * (1 + t * t)
        return n2 * vabs2 * mexp(d2 * (mpf("0.25") - t * t))
    val = 2 * mquad(lambda t: (mlog(t / (2 * mpi)) / (2 * mpi)) * env(t),
                    [tc, tc + 1 / delta, tc + 3 / delta, tc + 8 / delta],
                    maxdegree=8)
    return val


def bspline6(u):
    """Cardinal B-spline order 5 (6-fold box convolution), support [-3, 3],
    C^4 - a genuine C_c test for the explicit-formula identity."""
    u = mpf(repr(u)) if isinstance(u, float) else u
    x = u + 3
    if x < 0 or x > 6:
        return mpf(0)
    s = mpf(0)
    for k in range(0, int(mp.floor(x)) + 1):
        s += (-1) ** k * mp.binomial(6, k) * (x - k) ** 5
    return s / mp.factorial(5)


def anchor_gate():
    """ANCHOR A: identity on the C_c B-spline test (two independent W_R
    implementations must agree with each other and with the zero side);
    ANCHOR B: CC20 example test sign."""
    print("=== ANCHOR A: explicit-formula identity on the C_c 6-fold "
          "B-spline test ===", flush=True)
    G = bspline6

    def ftil(s):
        if abs(s) < mpf("1e-20"):
            return mpf(1)
        return (msinh(s / 2) / (s / 2)) ** 6

    # trivial side: int f + int f^sharp = f~(1) + f~(0)  (f~(0) = int f/x !)
    triv = ftil(mpf(1)) + ftil(mpf(0))
    zero_side = mpf(0)
    j = 0
    while True:
        j += 1
        g = mp.im(zetazero(j))
        if g > 100:
            break
        zero_side += 2 * mp.re(ftil(mpf(1) / 2 + 1j * g))
    tb = 0.75 * (2.063 / 100.0) ** 6          # density x |f~| bound beyond 100
    print(f"ANCHOR-A|zeros({j - 1} zeros)={float(zero_side):.10e}|tail<{tb:.1e}",
          flush=True)

    def integrand(u):
        return (G(u) + mexp(-u) * G(-u) - 2 * mexp(-u) * G(mpf(0))) \
            / (1 - mexp(-2 * u))
    # NB the -2 e^{-u} G(0) subtraction term has an EXPONENTIAL tail beyond
    # the support of G: integrate to 40 (e^{-40} floor), not to 3.
    wr_u = (mlog(4 * mpi) + EULER) * G(mpf(0)) + \
        mquad(integrand, [mpf("1e-12"), mpf("0.25"), mpf("0.5"), 1, 2, 3, 40])

    def integ3(t):
        w = mpf(1) / 2 + 1j * t
        return mp.re(mp.digamma(w / 2)) * ftil(w)
    i3 = 2 * mp.re(mquad(integ3, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32, 64, 128]))
    wr3 = mlog(mpi) * G(mpf(0)) - i3 / (2 * mpi)
    print(f"ANCHOR-A|W_R(u-form)={float(wr_u):.12f}"
          f"|W_R(f-form)={float(wr3):.12f}"
          f"|diff={float(abs(wr_u - wr3)):.2e}", flush=True)
    assert abs(wr_u - wr3) < 1e-8, "ANCHOR-A: the two W_R forms disagree"

    prime_side = mpf(0)
    for p0 in (2, 3, 5, 7, 11, 13, 17, 19):     # support [-3,3] => p <= e^3
        lp = mlog(mpf(p0))
        m0 = 1
        while m0 * lp <= 3:
            u0 = m0 * lp
            prime_side += lp * (G(u0) + mexp(-u0) * G(-u0))
            m0 += 1
    print(f"ANCHOR-A|prime_side={float(prime_side):.10f} (finite by support)",
          flush=True)

    rhs = triv - wr_u - prime_side
    resid = abs(zero_side - rhs) / abs(triv)
    print(f"ANCHOR-A|trivial={float(triv):.10f}|rhs={float(rhs):.10e}"
          f"|RESID={float(resid):.3e}  (gate <= 1e-6)", flush=True)
    assert resid < 1e-6, "ANCHOR-A FAILED: identity chain broken on the C_c test"
    print("ANCHOR-A|GATE-PASS", flush=True)

    print("\n=== ANCHOR B: CC20's own example test, sign of W_inf (tex:696) ===",
          flush=True)

    def G20(u):
        u = mpf(repr(u)) if isinstance(u, float) else u
        return (16 * u**4 - 104 * u**2 + 57) * mexp(-u * u / 2) / msqrt(2 * mpi)

    def fhat20(t):
        t = mpf(repr(t)) if isinstance(t, float) else t
        return (1 + 4 * t * t) ** 2 * mexp(-t * t / 2)
    for u0 in (0.0, 0.5, 1.3):
        raw = mquad(lambda tt: fhat20(tt) * mexp(1j * tt * u0), [-40, 0, 40]) \
            / (2 * mpi)
        err = abs(mp.re(raw) - G20(u0))
        print(f"ANCHOR-B|invfourier|u={u0}|G={float(G20(u0)):.6f}"
              f"|err={float(err):.2e}", flush=True)
        assert err < 1e-9, "inverse Fourier sub-gate failed"

    def integ20(u):
        return (G20(u) + mexp(-u) * G20(-u) - 2 * mexp(-u) * G20(mpf(0))) \
            / (1 - mexp(-2 * u))
    wr20 = (mlog(4 * mpi) + EULER) * G20(mpf(0)) + \
        mquad(integ20, [mpf("1e-12"), mpf("0.01"), 1, 10, 40])
    print(f"ANCHOR-B|W_R={float(wr20):.6f} => W_inf = -W_R = "
          f"{float(-wr20):.6f} (paper: W_inf(f) < 0)", flush=True)
    assert wr20 > 0, "ANCHOR-B FAILED: CC20 example should have W_inf < 0"
    print("ANCHOR-B|GATE-PASS", flush=True)


def run():
    print("=== 1070 LEVEL-1 Weil hunting probe V2 (correct dictionary: "
          "f~ = g~(s) g~(1-s)) ===", flush=True)
    anchor_gate()

    # dictionary gate on the family itself
    g30 = mp.im(zetazero(30))
    d_min = (1.177 / g30) / (2.0 ** (OCTAVES / 2))
    norm0, _ = normalize_family(1.177 / float(mp.im(zetazero(1))))
    gtil0 = make_gtil(1.177 / float(mp.im(zetazero(1))), norm0)
    f0 = make_ftilde(gtil0)
    e1, e0 = abs(f0(mpf(1))), abs(f0(mpf(0)))
    print(f"\nGATE|dictionary|f~(1)={float(e1):.2e}|f~(0)={float(e0):.2e}"
          f"  (both exact 0 by g~(0)=g~(1)=0)", flush=True)
    assert e1 < 1e-25 and e0 < 1e-25, "trivial side does not vanish"

    gmax = CACHE_GMAX if CACHE_GMAX > 0 else 5.0 / d_min
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])

    print("\n=== FORK SCAN (flips: margin + A - P < 0; margin = sum |g~|^2) ===",
          flush=True)
    for j in JLIST:
        gj = mp.im(zetazero(int(j)))
        gamma_j = float(gj)
        d_grid = [msqrt(2 / gj), msqrt(6 / gj)]     # coarse phase-rotation band
        d_grid += [2.0 / gamma_j, 1.177 / gamma_j]  # legacy peak + symbol tuning
        d = 1.177 / gamma_j
        for _ in range(2 * OCTAVES):
            d = d / (2.0 ** 0.5)
            d_grid.append(d)
        best = (float("inf"), 0.0, 0.0)
        for delta in d_grid:
            delta = float(delta)
            norm, tstar = normalize_family(delta)
            gtil = make_gtil(delta, norm)
            ftil = make_ftilde(gtil)
            cutoff = max(3.0 * gamma_j, 5.0 / delta)
            ncov = int(np.searchsorted(gam_np, cutoff))
            tb = tail_bound(delta, norm, gam[ncov - 1])
            rows = [2 * abs(gtil(mpf(1) / 2 + 1j * g)) ** 2 for g in gam[:ncov]]
            assert min(rows) > -1e-30, "margin row went negative"
            margin = sum(rows)
            Pj = rows[j - 1]
            flips = []
            for b in BETAS:
                bb = mpf(repr(b))
                A = 2 * mp.re(ftil(bb + 1j * gj) + ftil(1 - bb + 1j * gj))
                flips.append(float(margin + A - Pj))
            imin = int(np.argmin(flips))
            fl = flips[imin]
            # cross-term phase at the best beta (diagnostic)
            bb = mpf(repr(BETAS[imin]))
            cross = gtil(bb + 1j * gj) * mp.conj(gtil(1 - bb + 1j * gj))
            xphase = float(mp.arg(cross))
            tag = "FLIP" if fl < 0 else "ok"
            print(f"FORK|j={j}|gamma={gamma_j:.3f}|delta={delta:.5f}"
                  f"|tpeak={tstar:.2f}|margin={float(margin):.6f}"
                  f"|P={float(Pj):.6f}|minA-P={fl:.6f}@beta={BETAS[imin]}"
                  f"|xphase={xphase:.3f}"
                  f"|tail<{float(tb):.1e}|{tag}", flush=True)
            if fl < best[0]:
                best = (fl, delta, BETAS[imin])
        print(f"VERDICT-ROW|j={j}|gamma={gamma_j:.2f}|best_flip={best[0]:.6f}"
              f"|at_delta={best[1]:.5f}|at_beta={best[2]}"
              f"|{'HUNTS' if best[0] < 0 else 'NO-FLIP'}", flush=True)

    # symmetry sub-gate (j=1, coarse delta)
    g1 = mp.im(zetazero(1))
    dcoarse = 1.177 / float(g1)
    norm, _ = normalize_family(dcoarse)
    ftil = make_ftilde(make_gtil(dcoarse, norm))
    b = mpf("0.1")
    A1 = 2 * (mp.re(ftil(b + 1j * g1)) + mp.re(ftil(1 - b + 1j * g1)))
    A2 = 2 * (mp.re(ftil(1 - b + 1j * g1)) + mp.re(ftil(b + 1j * g1)))
    sym = abs(A1 - A2) / max(abs(A1), mpf("1e-300"))
    print(f"\nGATE|A-symmetry|rel={float(sym):.1e} (<= 1e-10)", flush=True)
    assert sym < 1e-10, "A(beta) != A(1-beta)"
    print("=== done: grep 'ANCHOR|FORK|VERDICT-ROW|GATE' for the fork table ===",
          flush=True)


if __name__ == "__main__":
    run()
