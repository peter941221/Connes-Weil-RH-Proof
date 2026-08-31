# 1077 - consumer #2 pinning: explicit triple-vanishing detector + field #4 sign.
#
# Design record: 1077_pinned_detector_sign.md (fork stated BEFORE the run).
# Follows 1075 (F-A: the {0,1}-killing symmetric family flips zero #2 at O(1)
# scale, thin sink; single-detector reach = zeros #1 AND #2).
#
# What is new here (vs the committed 1071 machinery, which we IMPORT verbatim):
#   A completion factor (s - 1/2)^2 added to the engineered family.  The pinned
#   detector is
#       g_3(s) = N' * s(1-s) * (s - 1/2)^2 * exp((-d^2 + i mu) * s(1-s)),
#   which vanishes EXACTLY at the whole triple {0, 1/2, 1} by construction
#   (no interpolation: s(1-s)=0 kills {0,1}, (s-1/2)^2=0 kills 1/2), is fully
#   symmetric under s -> 1-s, and detects the pinned off-line zero rho_2.
#   This delivers BOTH halves of record 1077's mandate in one probe:
#     (a) an explicit NAMED g with a closed form and an explicit support window;
#     (b) the field #4 sign at zero #2, read as qw(g) = -archimedeanTerm(g^box),
#         i.e. fl = margin0 + A - Pj  < 0  <=>  archimedeanTerm > 0.
#
# Why the completion is a clean delta on top of 1071 (not a rewrite):
#   * mu* only gains one term: to keep arg g_3(rho)^2 = pi we must absorb the
#     fixed phase 4 arg(rho - 1/2) from the extra factor, so
#       mu_3* = [pi/2 - arg V_F(rho) - 2 arg(rho - 1/2) + d^2 y] / x.
#     With the (s-1/2)^2 factor removed this reduces EXACTLY to 1071's mu_star;
#     we assert that reduction as a gate (CONFIRM-REDUCTION).
#   * On-line masses stay mu-independent: on s = 1/2 + it, q = s(1-s) = t^2+1/4
#     is REAL, so |exp((-d^2+i mu)q)| = e^{-d^2 q} for every mu (same reason as
#     the committed MU-INV gate).  The completion only adds a real factor t^2.
#   * Normalization: peak of |g_3(1/2+it)| is mu-independent, so N' is found by a
#     one-shot on-line grid (peak set to 1) - the same O(1)-scale convention as
#     1075, keeping wall/lever comparable and the e^{-2} clause meaningful.
#   * tail_bound3 carries the extra t^4 decay so the printed tail is a true g_3
#     envelope (the completion makes g_3 decay STRICTLY faster on-line).
#
# Flip semantics UNCHANGED from 1075: fl = margin0 + A - Pj < 0 => certificate
# sinks; O(1)-scale only if lever AND wall are both >= e^{-2} at the row.
# ANCHOR-A/ANCHOR-B gates: imported verbatim (family-independent sign chain).
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with mpmath python -u \
#      docs/proofs/1077_pinned_detector_sign_probe.py > /home/peter/1077_probe.log 2>&1; \
#      echo DONE-RC=$?'
# Env: JLIST_1077, CDLIST_1077, BETAS_1077, CACHE_GMAX_1077

import importlib.util
import json
import os

from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, quad as mquad

mp.dps = 30

# ---- reuse the committed 1071 machinery verbatim (ANCHOR gates + cache) -----
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1071", os.path.join(_here, "1071_engineered_weil_hunt_probe.py"))
assert _spec is not None and _spec.loader is not None, \
    "committed 1071 probe not found next to this file"
p1071 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1071)

vf0 = p1071.vf0          # V_F(s) = s (s - 1), symmetric, kills {0,1}
qsym = p1071.qsym        # w = s (1 - s), invariant under s -> 1-s
zero_cache = p1071.zero_cache   # persisted zero cache, reused
anchor_gate = p1071.anchor_gate  # ANCHOR-A + B, verbatim

JLIST = json.loads(os.environ.get("JLIST_1077", "[2, 3]"))
# c-lattice re-scan straddles the 1075 valley at cd* = 1.20 (interior minimum).
CDLIST = json.loads(os.environ.get("CDLIST_1077",
                                   "[1.00, 1.05, 1.10, 1.15, 1.20, 1.25, "
                                   "1.30, 1.35, 1.40]"))
# beta extended PAST the 1075 grid edge (0.46) to test the recorded caveat that
# deeper flips may exist; stays < 1/2 so rho stays genuinely off-line.
BETAS = json.loads(os.environ.get("BETAS_1077",
                                  "[0.38, 0.40, 0.42, 0.44, 0.46, 0.48]"))
CACHE_GMAX = float(os.environ.get("CACHE_GMAX_1077", "0"))  # 0 => auto


def make_g3(delta, norm, mu):
    """g_3(s) = N' * s(1-s) (s-1/2)^2 * exp((-d^2 + i mu) s(1-s)).

    Symmetric: g_3(1-s) = g_3(s).  Vanishes EXACTLY at {0, 1/2, 1}."""
    c = -delta * delta + 1j * mu

    def g3(s):
        return norm * vf0(s) * (s - mpf("0.5")) ** 2 * mexp(c * qsym(s))
    return g3


def normalize_family3(delta, npts=800):
    """N' so that peak_t |g_3(1/2 + i t)| = 1 (mu-independent on-line peak).

    On s = 1/2+it: |vf0| = q = t^2+1/4, |(s-1/2)^2| = t^2,
    and |exp| = e^{-d^2 q}.  Maximize the magnitude over a on-line grid."""
    d2 = delta * delta

    def mag(t):
        q = t * t + mpf("0.25")
        # |g_3(1/2+it)| with N'=1:  |vf0| = q,  |(s-1/2)^2| = t^2,  |exp| = e^{-d2 q}
        return q * (t * t) * mexp(-d2 * q)

    best, tb = mpf(0), mpf(0)
    hi = 6.0 / float(delta)               # well past the decay of e^{-d^2(t^2+1/4)}
    for k in range(1, npts + 1):
        t = mpf(hi) * (mpf(k) / mpf(npts))
        v = mag(t)
        if v > best:
            best, tb = v, t
    norm = mpf(1) / best
    return norm, float(tb)


def mu_3_star(delta, beta, gamma):
    """mu setting arg g_3(rho)^2 = pi.

    q = s(1-s) = x + i y at rho;  V_F = vf0(rho).  The completion adds the fixed
    phase 4 arg(rho-1/2), so mu absorbs -2 arg(rho-1/2):
        mu_3* = [pi/2 - argV - 2 arg(rho-1/2) + d^2 y] / x.
    Reduces to p1071.mu_star when the (s-1/2)^2 factor is removed."""
    q = qsym(beta + 1j * gamma)
    x, y = mp.re(q), mp.im(q)
    av = mp.arg(vf0(beta + 1j * gamma))
    argcmh = mp.arg((beta - mpf("0.5")) + 1j * gamma)   # arg(rho - 1/2)
    return (mpi / 2 - av - 2 * argcmh + delta * delta * y) / x


def tail_bound3(delta, norm, tc):
    """2 * int_tc^inf density(t) |g_3(1/2+it)|^2 dt; envelope N'^2 q^2 t^4 e^{-2d^2q}."""
    d2, n2 = delta * delta, norm * norm

    def env(t):
        q = t * t + mpf("0.25")
        return n2 * q * q * (t * t) ** 2 * mexp(-2 * d2 * q)
    val = 2 * mquad(lambda t: (mlog(t / (2 * mpi)) / (2 * mpi)) * env(t),
                    [tc, tc + 1 / delta, tc + 3 / delta, tc + 8 / delta],
                    maxdegree=8)
    return val


def run():
    print("=== 1077 consumer #2 pinning: triple-vanishing detector g_3 ===",
          flush=True)
    anchor_gate()

    # ---- family gates (representative d0; vanishing/symmetry are norm/mu-free)
    import numpy as np
    d0 = mpf("0.7") / mp.im(__import__("mpmath").zetazero(2))
    norm0, _ = normalize_family3(d0)
    g0 = make_g3(d0, norm0, mpf("0.3"))

    sym_err = max(abs(g0(s) - g0(1 - s)) / abs(g0(s))
                  for s in (mpf("0.3") + 1j * 2, mpf("1.7") + 1j * 9,
                            mpf("-0.2") + 1j * 20))
    print(f"\nGATE|symmetry|g_3(1-s)=g_3(s)|rel={float(sym_err):.2e}  "
          f"(<= 1e-25)", flush=True)
    assert sym_err < 1e-25, "family is not symmetric"

    # TRIPLE-vanishing: the whole node set {0, 1/2, 1} must be exactly zero.
    tv = {}
    for name, snode in (("zero", mpf(0)), ("half", mpf("0.5")), ("one", mpf(1))):
        e = abs(g0(snode))
        tv[name] = float(e)
        print(f"GATE|triple-vanishing|g_3({name})={e:.2e}", flush=True)
    assert max(tv.values()) < 1e-25, "not all three nodes vanish"

    # dictionary: trivial side of f_3~=g_3^2 vanishes (stronger than {0,1}).
    def ftil(s):
        return g0(s) * g0(1 - s)
    e1, e0 = abs(ftil(mpf(1))), abs(ftil(mpf(0)))
    print(f"GATE|dictionary|f~3(1)={e1:.2e}|f~3(0)={e0:.2e}", flush=True)
    assert e1 < 1e-25 and e0 < 1e-25, "trivial side does not vanish"

    # CONFIRM-REDUCTION: mu_3* + 2 arg(rho-1/2)/x == p1071.mu_star exactly.
    g2 = mp.im(__import__("mpmath").zetazero(2))
    bb = mpf("0.46")
    q = qsym(bb + 1j * g2)
    x = mp.re(q)
    argcmh = mp.arg((bb - mpf("0.5")) + 1j * g2)
    resid_red = abs(mu_3_star(d0, bb, g2) + 2 * argcmh / x
                    - p1071.mu_star(d0, bb, g2))
    print(f"GATE|confirm-reduction|mu_3*+corr vs mu_1071*|resid={float(resid_red):.2e}"
          f"  (<= 1e-25)", flush=True)
    assert resid_red < 1e-25, "completion phase correction does not reduce to 1071"

    d_min = mpf(str(min(CDLIST))) / mp.im(__import__("mpmath").zetazero(max(JLIST)))
    gmax = CACHE_GMAX if CACHE_GMAX > 0 else min(5.0 / float(d_min), 6000.0)
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])

    print("\n=== FORK SCAN (flips: fl = margin + A - P < 0; A = 4 Re g_3^2) ===",
          flush=True)
    best_per_j = {}
    for j in JLIST:
        gj = mp.im(__import__("mpmath").zetazero(int(j)))
        gamma_j = float(gj)
        for cd in CDLIST:
            delta = mpf(str(cd)) / gj
            norm, _ = normalize_family3(delta)
            g0m = make_g3(delta, norm, mpf(0))
            cutoff = max(3.0 * gamma_j, 5.0 / float(delta))
            ncov = int(np.searchsorted(gam_np, cutoff))
            tb = tail_bound3(delta, norm, gam[ncov - 1])
            rows = [2 * abs(g0m(mpf(1) / 2 + 1j * g)) ** 2 for g in gam[:ncov]]
            margin0 = sum(rows)
            Pj = rows[j - 1]
            wall = margin0 - Pj
            for beta in BETAS:
                bb = mpf(repr(beta))
                for mutag, mu in (("mu=0", mpf(0)),
                                  ("mu*", mu_3_star(delta, bb, gj))):
                    g3 = g0m if mu == 0 else make_g3(delta, norm, mu)
                    A = 4 * mp.re(g3(bb + 1j * gj) ** 2)
                    lever = 4 * abs(g3(bb + 1j * gj)) ** 2
                    fl = float(margin0 + A - Pj)
                    xphase = float(mp.arg(g3(bb + 1j * gj) ** 2))
                    if mutag == "mu*":
                        pherr = min(abs(xphase - mpi), abs(xphase + mpi))
                        assert pherr < 1e-5, "phase gate: mu_3* missed pi"
                        minv = sum(2 * abs(g3(mpf(1) / 2 + 1j * g)) ** 2
                                   for g in gam[:ncov])
                        rel = abs(minv - margin0) / margin0
                        assert rel < 1e-20, "mu moved the on-line masses"
                    tag = "FLIP" if fl < 0 else "ok"
                    wl = float(wall / lever) if lever > 0 else float("inf")
                    scale_ok = (lever >= mpf(1) / mexp(2)) and \
                               (wall >= mpf(1) / mexp(2))
                    print(f"FORK|j={j}|gamma={gamma_j:.3f}|cd={cd}"
                          f"|beta={beta}|{mutag}"
                          f"|margin={float(margin0):.6f}|P={float(Pj):.6f}"
                          f"|A={float(A):.6f}|wall={float(wall):.6f}"
                          f"|lever={float(lever):.6f}|wall/lever={wl:.3f}"
                          f"|xphase={xphase:.4f}"
                          f"|flip={fl:.6f}|tail<{float(tb):.1e}"
                          f"|O1={'Y' if scale_ok else 'n'}|{tag}",
                          flush=True)
                    if mutag == "mu*" and fl < 0:
                        cur = best_per_j.get(j)
                        if cur is None or fl < cur[0]:   # cur[0] = stored flip (most negative wins)
                            best_per_j[j] = (fl, cd, beta, float(wall),
                                             float(lever))
        print(f"VERDICT-ROW|j={j}|gamma={gamma_j:.2f}", flush=True)

    print("\n=== BEST FLIP ROW PER j (mu* only) ===", flush=True)
    for j in JLIST:
        if j in best_per_j:
            fl, cd, beta, wall, lever = best_per_j[j]
            sinkpct = 100.0 * abs(fl) / lever if lever > 0 else float("nan")
            print(f"BEST|j={j}|flip={fl:.6f}@cd={cd},beta={beta}"
                  f"|wall/lever={(wall/lever):.3f}|sink={sinkpct:.2f}% of lever",
                  flush=True)
        else:
            print(f"BEST|j={j}|no flip (min fl >= 0)", flush=True)

    print("=== done: grep 'ANCHOR|FORK|VERDICT-ROW|GATE|BEST' for the fork table ===",
          flush=True)


if __name__ == "__main__":
    run()
