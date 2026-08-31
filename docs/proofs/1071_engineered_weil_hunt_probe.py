# 1071 - LEVEL-1 slice 2: engineered (Yoshida-type) Weil hunt (closed form).
#
# Design record: 1071_engineered_weil_hunt.md (fork stated BEFORE the run).
# Follows 1070 (H3': smooth Gaussian family cannot hunt; next slice = ONE
# engineered family through the SAME pipeline, only g~ changes).
#
# Family E:  g~(s) = N(d) * s(s-1) * exp((-d^2 + i mu) * s(1-s)),  F = {0,1}.
#   Symmetric: g~(1-s) = g~(s)  =>  f~(s) = g~(s)^2 on the s <-> 1-s orbit,
#   A_j = 4 Re g~(b+i g)^2 = lever * cos(phi),  phi = 2 arg g~(b+i g) FREE
#   via mu* ~ pi/(2 g^2)  (magnitude cost e^{O(1/g)} ~ 1: no exponential
#   suppression).  mu leaves ON-LINE masses unchanged (hard gate).
# Same flip semantics as 1070: margin + A - P < 0 (certificate sinks).
# ANCHOR A/B gates: verbatim 1070 (family-independent).
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with mpmath python -u \
#      docs/proofs/1071_engineered_weil_hunt_probe.py > /home/peter/1071_probe.log 2>&1; \
#      echo DONE-RC=$?'
# Env: JLIST_1071, DELTAS_1071, BETA_1071, CACHE_GMAX_1071

import json
import os

import numpy as np
from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, sqrt as msqrt, \
    sinh as msinh, zetazero, quad as mquad

mp.dps = 30

JLIST = json.loads(os.environ.get("JLIST_1071", "[1, 2, 3, 5, 10, 20, 30]"))
DLIST = json.loads(os.environ.get("DELTAS_1071", "[0.3, 0.6, 1.0, 2.0]"))
BETAS = json.loads(os.environ.get("BETA_1071",
                                  "[0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.45]"))
CACHE_GMAX = float(os.environ.get("CACHE_GMAX_1071", "0"))  # 0 => auto

EULER = mpf("0.57721566490153286060651209008240243104215933593992")


def vf0(s):
    """V_F(s) = s (s - 1) for F = {0, 1} (symmetric: V(1-s) = V(s))."""
    return s * (s - 1)


def qsym(s):
    """The symmetric coordinate w = s (1 - s) (invariant under s -> 1-s)."""
    return s * (1 - s)


def make_gtil(delta, norm, mu):
    """g~(s) = N * s(s-1) * exp((-d^2 + i mu) s(1-s)); g~(1-s) = g~(s)."""
    c = -delta * delta + 1j * mu

    def gtil(s):
        return norm * vf0(s) * mexp(c * qsym(s))
    return gtil


def make_ftilde(gtil):
    """f~(s) = g~(s) g~(1-s)  (Mellin convolution theorem; UNCHANGED 1070)."""

    def ftil(s):
        return gtil(s) * gtil(1 - s)
    return ftil


def normalize_family(delta):
    """N = delta^2 e (closed form: max_Q>=1/4 Q e^{-d^2 Q} at Q = 1/d^2)."""
    norm = delta * delta * mp.e
    tstar = msqrt(1 / (delta * delta) - mpf(1) / 4)
    peak = norm * vf0(mpf(1) / 2 + 1j * tstar) \
        * mexp(-delta * delta * (tstar * tstar + mpf(1) / 4))
    assert abs(abs(peak) - 1) < 1e-20, "closed-form normalization failed"
    return norm, float(tstar)


def mu_star(delta, beta, gamma):
    """mu setting phi = pi:  phi = 2(argV + mu x - d^2 y), q = x + i y."""
    q = qsym(beta + 1j * gamma)
    x, y = mp.re(q), mp.im(q)
    av = mp.arg(vf0(beta + 1j * gamma))
    return (mpi / 2 - av + delta * delta * y) / x


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
    """2 * int_tc^inf density(t) |g~(1/2+it)|^2 dt, envelope N^2 Q^2 e^{-2d^2Q}."""
    d2, n2 = delta * delta, norm * norm

    def env(t):
        q = t * t + mpf("0.25")
        return n2 * q * q * mexp(-2 * d2 * q)
    val = 2 * mquad(lambda t: (mlog(t / (2 * mpi)) / (2 * mpi)) * env(t),
                    [tc, tc + 1 / delta, tc + 3 / delta, tc + 8 / delta],
                    maxdegree=8)
    return val


def bspline6(u):
    """Cardinal B-spline order 5 (6-fold box convolution), support [-3, 3]."""
    u = mpf(repr(u)) if isinstance(u, float) else u
    x = u + 3
    if x < 0 or x > 6:
        return mpf(0)
    s = mpf(0)
    for k in range(0, int(mp.floor(x)) + 1):
        s += (-1) ** k * mp.binomial(6, k) * (x - k) ** 5
    return s / mp.factorial(5)


def anchor_gate():
    """ANCHOR A + B: verbatim 1070 (family-independent sign-chain validation)."""
    print("=== ANCHOR A: explicit-formula identity on the C_c 6-fold "
          "B-spline test ===", flush=True)
    G = bspline6

    def ftil(s):
        if abs(s) < mpf("1e-20"):
            return mpf(1)
        return (msinh(s / 2) / (s / 2)) ** 6

    triv = ftil(mpf(1)) + ftil(mpf(0))
    zero_side = mpf(0)
    j = 0
    while True:
        j += 1
        g = mp.im(zetazero(j))
        if g > 100:
            break
        zero_side += 2 * mp.re(ftil(mpf(1) / 2 + 1j * g))
    tb = 0.75 * (2.063 / 100.0) ** 6
    print(f"ANCHOR-A|zeros({j - 1} zeros)={float(zero_side):.10e}|tail<{tb:.1e}",
          flush=True)

    def integrand(u):
        return (G(u) + mexp(-u) * G(-u) - 2 * mexp(-u) * G(mpf(0))) \
            / (1 - mexp(-2 * u))
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
    for p0 in (2, 3, 5, 7, 11, 13, 17, 19):
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
    assert resid < 1e-6, "ANCHOR-A FAILED: identity chain broken"
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
    assert wr20 > 0, "ANCHOR-B FAILED"
    print("ANCHOR-B|GATE-PASS", flush=True)


def run():
    print("=== 1071 LEVEL-1 engineered Weil hunt (symmetric family, free "
          "phase via mu) ===", flush=True)
    anchor_gate()

    # family gates
    d0 = mpf("0.7")
    norm0, _ = normalize_family(d0)
    gt0 = make_gtil(d0, norm0, mpf("0.3"))
    sym_err = max(abs(gt0(s) - gt0(1 - s)) / abs(gt0(s))
                  for s in (mpf("0.3") + 1j * 2, mpf("1.7") + 1j * 9,
                            mpf("-0.2") + 1j * 20))
    print(f"\nGATE|symmetry|g~(1-s)=g~(s)|rel={float(sym_err):.2e}  "
          f"(<= 1e-25)", flush=True)
    assert sym_err < 1e-25, "family is not symmetric"

    g1 = mp.im(zetazero(1))
    assert g1 > 0
    f0 = make_ftilde(make_gtil(d0, norm0, mpf(0)))
    e1, e0 = abs(f0(mpf(1))), abs(f0(mpf(0)))
    print(f"GATE|dictionary|f~(1)={float(e1):.2e}|f~(0)={float(e0):.2e}",
          flush=True)
    assert e1 < 1e-25 and e0 < 1e-25, "trivial side does not vanish"

    d_min = mpf(str(min(DLIST))) / mp.im(zetazero(max(JLIST)))
    gmax = CACHE_GMAX if CACHE_GMAX > 0 else min(5.0 / float(d_min), 6000.0)
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])

    print("\n=== FORK SCAN (flips: margin + A - P < 0; A = 4 Re g~^2) ===",
          flush=True)
    for j in JLIST:
        gj = mp.im(zetazero(int(j)))
        gamma_j = float(gj)
        for cd in DLIST:
            delta = mpf(str(cd)) / gj
            norm, tstar = normalize_family(delta)
            gtil0 = make_gtil(delta, norm, mpf(0))
            cutoff = max(3.0 * gamma_j, 5.0 / float(delta))
            ncov = int(np.searchsorted(gam_np, cutoff))
            tb = tail_bound(delta, norm, gam[ncov - 1])
            rows = [2 * abs(gtil0(mpf(1) / 2 + 1j * g)) ** 2 for g in gam[:ncov]]
            margin0 = sum(rows)
            Pj = rows[j - 1]
            wall = margin0 - Pj
            for beta in BETAS:
                bb = mpf(repr(beta))
                for mutag, mu in (("mu=0", mpf(0)),
                                  ("mu*", mu_star(delta, bb, gj))):
                    gtil = gtil0 if mu == 0 else make_gtil(delta, norm, mu)
                    A = 4 * mp.re(gtil(bb + 1j * gj) ** 2)
                    lever = 4 * abs(gtil(bb + 1j * gj)) ** 2
                    fl = float(margin0 + A - Pj)
                    xphase = float(mp.arg(gtil(bb + 1j * gj) ** 2))
                    if mutag == "mu*":
                        pherr = abs(abs(xphase - mpi) - mpi)
                        assert pherr < 1e-5, "phase gate: mu* missed pi"
                        minv = sum(2 * abs(gtil(mpf(1) / 2 + 1j * g)) ** 2
                                   for g in gam[:ncov])
                        rel = abs(minv - margin0) / margin0
                        assert rel < 1e-20, "mu moved the on-line masses"
                    tag = "FLIP" if fl < 0 else "ok"
                    wl = float(wall / lever) if lever > 0 else float("inf")
                    print(f"FORK|j={j}|gamma={gamma_j:.3f}|delta={float(delta):.6f}"
                          f"|beta={beta}|{mutag}"
                          f"|margin={float(margin0):.6f}|P={float(Pj):.6f}"
                          f"|A={float(A):.6f}|wall={float(wall):.6f}"
                          f"|lever={float(lever):.6f}|wall/lever={wl:.3f}"
                          f"|xphase={xphase:.4f}"
                          f"|flip={fl:.6f}|tail<{float(tb):.1e}|{tag}",
                          flush=True)
        print(f"VERDICT-ROW|j={j}|gamma={gamma_j:.2f}", flush=True)

    print("=== done: grep 'ANCHOR|FORK|VERDICT-ROW|GATE' for the fork table ===",
          flush=True)


if __name__ == "__main__":
    run()
