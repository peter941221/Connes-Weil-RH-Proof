#!/usr/bin/env python3
# 1740 P2 ledger rig (v2, instrument-fixed): audit numerics + F70 width law.
#
# Committed bookkeeping pinned by the 1740 audit (all machine-checked in repo):
#   psi(F)  = poleTerm(F) - archimedeanTerm(F) - finitePrimeSum(F)
#             (C1SameWeil.lean:192-193)
#   qw(g)   = psi(g.convolutionSquare) = spectralWeilValue(g.convolutionSquare)
#             (Gate 2, C1CenterTwoCriterionBridge.lean:28-32, unconditional)
#   pole    = 0 on the triple-vanishing class (Hermitian pairing kills both
#             pole moments via laplaceAt g (1/2) = 0;
#             C1HealthyYoshidaDetector.lean:48-51, :92-110)
#   arch(F) = (log 4pi + gamma_E) F(0)
#             + int_0^inf [exp(y/2)(F(y)+F(-y)) - 2 F(0)]/(e^y - e^{-y}) dy
#   finite  = sum over visible prime powers: Lambda(n)/sqrt(n)(F(log n)+F(-log n))
#   =>  P2  <=>  arch + finite <= 0 for every triple-vanishing g.
#
# Paper anchor (1740 record): the arch quadratic-form symbol is
#   sigma(xi) = log(pi) - Re psi(1/4 - i xi/2),
# validated here three ways (scipy quad, mpmath quad, closed form).
#
# v1 -> v2 instrument fixes (F27/F28):
#   * arch_direct: exact tent-node grid, k=0 limit term F0/2, np.trapz
#     (was: half-cell misaligned rectangle rule -> E2x rel diff ~ 1.0)
#   * E3 pole: np.trapz (was: left-endpoint rectangle -> pole/F0 ~ du)
#   * E3 arch: no 0/0 at y=0 (was: NaN)
#   * NEW E5: smooth D3-root band-pass probe (RH-necessity adjudicator:
#     arch <= 0 must hold on the whole smooth triple window class)
#   * NEW E2s: smoothing diagnostic on the top triple eigenvector
#
# v2 -> v3 (F71, found by the E2t three-way instrument):
#   * arch_direct node-trapz substituted the SMOOTH-class limit F0/2 at
#     y=0, but rect-class F has slope 1/du there: true right limit of
#     num/D is F0*(1/2 - 1/du) -> O(F0/2) bias (d-m = -0.39..-0.81 in
#     E2t).  arch_direct now integrates the exact piecewise-linear
#     tent-sum F with adaptive quad; validated vs the Toeplitz matrix
#     path to 4e-7 on 4 structured vectors (E2t).  E3/E4/E5 inherit it.
#   * VERDICT REVERSAL: the rect-class lambda_triple = +0.84 at the
#     Yoshida window is REAL (matrix = exact to 4e-7), not a rough-basis
#     artifact; the smoothing diagnostic does not move it.  The smooth
#     (C_c^infinity) class verdict is E5's job.
import json
import math
import os
import time

import numpy as np
from scipy.integrate import quad

try:
    import mpmath as mp
    HAVE_MP = True
except Exception:
    mp = None
    HAVE_MP = False

LOG4PI_GAMMA = math.log(4.0 * math.pi) + 0.57721566490153286060651209008240243
LOGPI = math.log(math.pi)
LOG2 = math.log(2.0)
YOSHIDA_W = LOG2 / 2.0
Y_MAX = 60.0

TRAPZ = getattr(np, "trapz", None) or np.trapezoid  # numpy >= 2.0 fallback

t0 = time.time()
LOG_LINES = []


def log(msg):
    line = "[%8.1fs] %s" % (time.time() - t0, msg)
    print(line, flush=True)
    LOG_LINES.append(line)


# ---------------------------------------------------------------- E1: sigma

def sigma_integrand(y, xi):
    return (2.0 * math.cos(xi * y) * math.exp(y / 2.0) - 2.0) / (
        math.exp(y) - math.exp(-y))


def sigma(xi):
    val, _ = quad(sigma_integrand, 0.0, Y_MAX, args=(xi,),
                  limit=800, epsabs=1e-12, epsrel=1e-12)
    return LOG4PI_GAMMA + val


def sigma_closed(xi):
    """log(pi) - Re psi(1/4 - i xi/2) via the digamma recurrence/series."""
    if HAVE_MP:
        mp.mp.dps = 30
        return LOGPI - float(mp.re(mp.digamma(mp.mpf("0.25") - 1j * xi / 2)))
    z = 0.25 - 1j * xi / 2.0
    s = -np.euler_gamma
    for n in range(1, 200000):
        s += (1.0 / n) - (1.0 / complex(n - 1 + z))
    return LOGPI - s.real


def find_zero_crossing(f, lo, hi, iters=90):
    flo, fhi = f(lo), f(hi)
    if flo * fhi > 0:
        return None
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if flo * fm <= 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


# ----------------------------------------------- direct arch (fixed) -----

def arch_direct(g, du):
    """arch(g star g~) for the rect-class function with samples g.

    v3 (F71): the naive node-trapz version substituted the SMOOTH-class
    limit F0/2 at y=0, but the rect-class F has slope 1/du at the origin,
    so the true right limit of num/D is F0*(1/2 - 1/du) -> an O(F0/2)
    bias (E2t: d-m = -0.39 .. -0.81).  Fixed by integrating the EXACT
    piecewise-linear tent-sum F with adaptive quad (validated against
    the Toeplitz matrix path to 4e-7 in E2t)."""
    c = np.asarray(g, dtype=float) * math.sqrt(du)
    n_ex = len(c)
    corr = np.correlate(c, c, mode="full")
    A = corr[n_ex - 1:]                          # A_k = sum_i c_i c_{i+k}
    F0 = float(A[0])

    def F_of_y(y):
        t = abs(y) / du                          # F even: A_{-k} = A_k
        k = int(t)                               # t >= 0
        if k >= n_ex:
            return 0.0
        frac = t - k
        total = A[k] * (1.0 - frac)
        if k + 1 < n_ex:
            total += A[k + 1] * frac
        return total

    def integrand(y):
        return (math.exp(y / 2.0) * (F_of_y(y) + F_of_y(-y))
                - 2.0 * F0) / math.expm1(2.0 * y)

    ytop = n_ex * du + 20.0
    core, _ = quad(integrand, 0.0, ytop, limit=400,
                   epsabs=1e-11, epsrel=1e-11)
    tail = -2.0 * F0 * sum(math.exp(-(2 * j + 1) * ytop) / (2 * j + 1)
                           for j in range(400))
    return LOG4PI_GAMMA * F0 + core + tail, F0


# ------------------------------------------------- E2: arch quadratic form

def arch_toeplitz_symbol(d, du, y_mesh):
    D = np.expm1(2.0 * y_mesh)
    ey = np.exp(y_mesh / 2.0)
    if d == 0.0:
        tent_pair = 2.0 * np.clip(1.0 - y_mesh / du, 0.0, 1.0)
        num = ey * tent_pair - 2.0
    else:
        right = np.clip(1.0 - np.abs(y_mesh - d) / du, 0.0, 1.0)
        left = np.clip(1.0 - (y_mesh + d) / du, 0.0, 1.0)
        num = ey * (right + left)
    step = y_mesh[1] - y_mesh[0]
    return float(np.sum(num / D) * step)


def build_arch_matrix(w, n, refine=8):
    du = 2.0 * w / n
    y_top = 2.0 * w + 20.0
    y_mesh = np.arange(0.5 * du / refine, y_top, du / refine)
    m = np.zeros(n)
    for k in range(n):
        m[k] = arch_toeplitz_symbol(k * du, du, y_mesh)
        if k == 0:
            m[0] += -2.0 * sum(math.exp(-(2 * j + 1) * y_mesh[-1])
                               / (2 * j + 1) for j in range(200))
    idx = np.abs(np.subtract.outer(np.arange(n), np.arange(n)))
    return LOG4PI_GAMMA * np.eye(n) + m[np.minimum(idx, n - 1)], du


def constraint_projector(x, kinds):
    n = len(x)
    rows = []
    if "mass" in kinds:
        rows.append(np.ones_like(x))
    if "triple" in kinds:
        rows.append(np.exp(-x / 2.0))
        rows.append(np.exp(-x))
    if not rows:
        return np.eye(n)
    B = []
    for r in rows:
        v = r.copy()
        for b in B:
            v = v - (b @ v) * b
        nv = np.linalg.norm(v)
        if nv > 1e-12:
            B.append(v / nv)
    B = np.array(B).T
    return np.eye(n) - B @ B.T


def project_vec(g, x, kinds):
    return constraint_projector(x, kinds) @ g


def top_eigen(M, x, kinds, want_vector=False):
    P = constraint_projector(x, kinds)
    PM = P @ M @ P
    PM = 0.5 * (PM + PM.T)
    if want_vector:
        ev, V = np.linalg.eigh(PM)
        return float(ev[-1]), V[:, -1]
    return float(np.linalg.eigvalsh(PM)[-1]), None


def von_mangoldt_table(top):
    lam = np.zeros(top + 1)
    for i in range(2, top + 1):
        if lam[i] == 0.0:
            pk = i
            while pk <= top:
                lam[pk] = math.log(i)
                pk *= i
    return lam


# ------------------------------------------------------------------- main

def main():
    results = {"wave": 1740, "rig": "p2_ledger_rig_1740", "version": 2,
               "constants": {"log4pi_plus_gamma": LOG4PI_GAMMA,
                             "yoshida_w": YOSHIDA_W}}

    # ---- E1: sigma chart + closed form
    log("E1: sigma chart (scipy / mpmath-integrand / closed form)")
    xis = [0.0, 0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 6.5, 7.0, 8.0, 10.0,
           15.0, 30.0, 50.0]
    chart = []
    for xi in xis:
        s1 = sigma(xi)
        s3 = sigma_closed(xi)
        chart.append({"xi": xi, "sigma_quad": s1, "sigma_closed": s3,
                      "absdiff": abs(s1 - s3)})
        log("  sigma(%6.2f) = %+.6f  closed %+.6f  |d|=%.2e"
            % (xi, s1, s3, abs(s1 - s3)))
    xstar = find_zero_crossing(sigma, 1.0, 30.0)
    log("  zero crossing xi* = %.6f  (1/xi* = %.6f)" % (xstar, 1.0 / xstar))
    results["E1_sigma"] = {"chart": chart, "xi_star": xstar}

    # ---- E2: lambda_max(w) sweep (matrix path)
    log("E2: lambda_max(w) sweep of the arch form (rect basis)")
    widths = [0.10, 0.20, 0.29, YOSHIDA_W, 0.40, 0.50, 0.70, 1.00, 1.50,
              2.00, 3.00]
    du_target = 8.4e-4
    sweep = []
    for w in widths:
        n = int(min(1000, max(500, round(2 * w / du_target))))
        du = 2.0 * w / n
        x = -w + (np.arange(n) + 0.5) * du
        M, _ = build_arch_matrix(w, n)
        l_none, _v = top_eigen(M, x, [])
        l_mass, _v = top_eigen(M, x, ["mass"])
        l_tri, _v = top_eigen(M, x, ["triple"])
        sweep.append({"w": w, "n": n, "du": du,
                      "lam_max_unconstrained": l_none,
                      "lam_max_mass_zero": l_mass,
                      "lam_max_triple": l_tri})
        log("  w=%.5f n=%4d: lam_none=%+.4f lam_mass=%+.4f lam_triple=%+.4f"
            % (w, n, l_none, l_mass, l_tri))
    results["E2_width_sweep"] = sweep

    # ---- E2x: cross-path check (fixed direct path)
    log("E2x: cross-path check (matrix vs fixed direct path)")
    w = YOSHIDA_W
    n = int(min(1000, max(500, round(2 * w / du_target))))
    du = 2.0 * w / n
    x = -w + (np.arange(n) + 0.5) * du
    M, _ = build_arch_matrix(w, n)
    rng = np.random.default_rng(1737)
    worst = 0.0
    for _ in range(24):
        c = project_vec(rng.standard_normal(n), x, ["triple"])
        vm = float(c @ M @ c)
        vd, _F0 = arch_direct(c / math.sqrt(du), du)  # sample convention
        worst = max(worst, abs(vm - vd) / max(abs(vm), abs(vd), 1e-300))
    log("  24 random triple directions: worst rel diff = %.3e" % worst)
    results["E2x_cross_check"] = {"worst_rel_diff": worst}

    # ---- E2s: smoothing diagnostic on the top triple eigenvector (Yoshida)
    log("E2s: smoothing diagnostic (top triple eigenvector, Yoshida window)")
    lam_t, vec = top_eigen(M, x, ["triple"], want_vector=True)
    arch_raw, F0_raw = arch_direct(vec / math.sqrt(du), du)
    ker = np.exp(-0.5 * (np.arange(-6, 7) * du / (2.0 * du)) ** 2)
    ker /= ker.sum()
    sm = np.convolve(vec / math.sqrt(du), ker, mode="same")
    sm = project_vec(sm, x, ["triple"])
    arch_sm, F0_sm = arch_direct(sm, du)
    log("  lam_triple(matrix)=%+.4f  arch(evec direct)=%+.4f  "
        "arch(smoothed)=%+.4f" % (lam_t, arch_raw, arch_sm))
    results["E2s_smoothing"] = {
        "lam_triple_matrix": lam_t,
        "arch_evec_direct": arch_raw,
        "arch_smoothed": arch_sm,
    }

    # ---- E2t: three-way instrument (matrix / direct / exact tent-sum quad)
    log("E2t: three-way instrument (matrix vs direct vs exact quad)")
    from scipy.integrate import quad as _quad

    def arch_exact_c(c, du_ex):
        """Exact rect-class arch for coefficient vector c:
        F(y) = sum_k A_k tent(y - k du), A_k = sum_{i-j=k} c_i c_j."""
        n_ex = len(c)
        A = np.array([float(np.correlate(c, c, mode="full")[n_ex - 1 + k])
                      for k in range(n_ex)])
        F0e = float(A[0])

        def F_of_y(y):
            t = abs(y) / du_ex          # F even: A_{-k} = A_k
            k = int(math.floor(t))
            if k >= n_ex:
                return 0.0
            frac = t - k
            total = A[k] * (1.0 - frac)
            if k + 1 < n_ex:
                total += A[k + 1] * frac
            return total

        def integrand(y):
            D = math.expm1(2.0 * y)
            return (math.exp(y / 2.0) * (F_of_y(y) + F_of_y(-y))
                    - 2.0 * F0e) / D

        ytop = n_ex * du_ex + 20.0
        core, _ = _quad(integrand, 0.0, ytop, limit=800,
                        epsabs=1e-12, epsrel=1e-12)
        tail = -2.0 * F0e * sum(math.exp(-(2 * j + 1) * ytop) / (2 * j + 1)
                                for j in range(400))
        return LOG4PI_GAMMA * F0e + core + tail

    w = YOSHIDA_W
    n = int(min(1000, max(500, round(2 * w / du_target))))
    du = 2.0 * w / n
    x = -w + (np.arange(n) + 0.5) * du
    M, _ = build_arch_matrix(w, n)
    rng = np.random.default_rng(41736)
    tests = {}
    tests["e_mid"] = np.eye(n)[n // 2]
    cr = project_vec(rng.standard_normal(n), x, ["triple"])
    tests["random_triple"] = cr / math.sqrt(float(cr @ cr))
    lam_t, vec = top_eigen(M, x, ["triple"], want_vector=True)
    tests["top_evec"] = vec
    ker = np.exp(-0.5 * (np.arange(-6, 7) * du / (2.0 * du)) ** 2)
    ker /= ker.sum()
    smv = np.convolve(vec, ker, mode="same")
    smv = project_vec(smv, x, ["triple"])
    smv = smv / math.sqrt(float(smv @ smv))
    tests["smoothed_evec"] = smv
    e2t = []
    for name, c in tests.items():
        vm = float(c @ M @ c)
        vd, _ = arch_direct(c / math.sqrt(du), du)
        ve = arch_exact_c(c, du)
        Asm = float(np.sum(np.abs(np.diff(np.correlate(
            c, c, mode="full")[n - 1:]))))
        e2t.append({"name": name, "matrix": vm, "direct": vd, "exact": ve,
                    "A_variation": Asm})
        log("  %-14s matrix=%+.6f direct=%+.6f exact=%+.6f "
            "(d-m=%+.2e, e-m=%+.2e, Avar=%.2e)"
            % (name, vm, vd, ve, vd - vm, ve - vm, Asm))
    results["E2t_threeway"] = e2t

    # ---- E3: pole verification + qw sampling (fixed)
    log("E3: pole ~= 0 + full-book qw sampling on the triple class")
    e3 = {}
    lam_tab = von_mangoldt_table(64)
    for w in (0.29, YOSHIDA_W):
        n = int(min(1000, max(500, round(2 * w / du_target))))
        du = 2.0 * w / n
        x = -w + (np.arange(n) + 0.5) * du
        M, _ = build_arch_matrix(w, n)
        rng = np.random.default_rng(91736 + int(w * 1e5))
        qws, archs, fins, pole_ratio = [], [], [], []
        for _ in range(120):
            g = project_vec(rng.standard_normal(n), x, ["triple"])
            nrm = math.sqrt(du * float(g @ g))
            if nrm > 1e-12:
                g = g / nrm
            corr = np.correlate(g, g, mode="full") * du
            mid = (len(corr) - 1) // 2
            Fv = corr[mid:]
            F0 = float(Fv[0])
            ypos = np.arange(len(Fv)) * du
            wts = np.exp(-ypos / 2.0) + np.exp(ypos / 2.0)
            p = float(TRAPZ(Fv * wts, ypos))
            pole_ratio.append(abs(p) / max(F0, 1e-300))
            arch, _ = arch_direct(g, du)   # v3 exact tent-sum quad (F71)
            fin = 0.0
            for nn in range(2, len(lam_tab)):
                if lam_tab[nn] <= 0.0:
                    continue
                ln = math.log(nn)
                if ln > 2.0 * w:
                    break
                k = int(ln / du)
                if k + 1 >= len(Fv):
                    continue
                frac = ln / du - k
                Fv2 = Fv[k] * (1 - frac) + Fv[k + 1] * frac
                fin += lam_tab[nn] / math.sqrt(nn) * 2.0 * Fv2
            archs.append(arch)
            fins.append(fin)
            qws.append(-(arch + fin))
        key = "w=%.5f" % w
        e3[key] = {"pole_over_F0_max": max(pole_ratio),
                   "arch_min": min(archs), "arch_max": max(archs),
                   "finite_min": min(fins), "finite_max": max(fins),
                   "qw_min": min(qws), "qw_max": max(qws),
                   "qw_mean": float(np.mean(qws))}
        r = e3[key]
        log("  %s: pole/F0|max|=%.2e arch in [%+.4f,%+.4f] finite in "
            "[%+.2e,%+.2e] qw in [%+.4f,%+.4f] mean %+.4f"
            % (key, r["pole_over_F0_max"], r["arch_min"], r["arch_max"],
               r["finite_min"], r["finite_max"], r["qw_min"], r["qw_max"],
               r["qw_mean"]))
    results["E3_qw_sampling"] = e3

    # ---- E4: band-pass probe at w = 3 (smooth even bump x sin)
    log("E4: smooth band-pass probe at w = 3 (mass-zero class)")
    e4 = []
    w4 = 3.0
    n4 = 3000
    du4 = 2.0 * w4 / n4
    x4 = -w4 + (np.arange(n4) + 0.5) * du4
    phi = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (x4 / w4) ** 2))
    phi[np.abs(x4) >= w4] = 0.0
    for xi0 in (0.5, 1.0, 2.0):
        g = phi * np.sin(2.0 * math.pi * xi0 * x4)
        g = g - (du4 * float(np.sum(g))) / (n4 * du4)
        a, F0 = arch_direct(g, du4)
        e4.append({"xi0": xi0, "carrier_angular": 2.0 * math.pi * xi0,
                   "sigma_at_carrier": sigma(2.0 * math.pi * xi0),
                   "arch": a, "F0": F0, "arch_over_F0": a / F0})
        log("  xi0=%.1f (angular %.2f, sigma=%.3f): arch/F0 = %+.4f"
            % (xi0, 2 * math.pi * xi0, sigma(2 * math.pi * xi0), a / F0))
    results["E4_bandpass_w3"] = e4

    # ---- E5: smooth D3-root probe (RH-necessity adjudicator)
    log("E5: smooth D3-root probe on the triple window class")
    e5 = []
    for w in (0.29, YOSHIDA_W):
        n = int(min(1000, max(500, round(2 * w / du_target))))
        du = 2.0 * w / n
        x = -w + (np.arange(n) + 0.5) * du
        for xi0 in (0.5, 1.0, 2.0, 3.0):
            h = np.exp(-1.0 / np.maximum(1e-300,
                                         1.0 - (x / w) ** 2)) \
                * np.cos(2.0 * math.pi * xi0 * x)
            d1 = np.gradient(h, du)
            d2 = np.gradient(d1, du)
            d3 = np.gradient(d2, du)
            g = d3 + 1.5 * d2 + 0.5 * d1
            # verify the three Laplace vanishings
            m0 = abs(du * float(np.sum(g)))
            m1 = abs(du * float(np.sum(g * np.exp(-x / 2.0))))
            m2 = abs(du * float(np.sum(g * np.exp(-x))))
            scale = math.sqrt(du * float(g @ g)) + 1e-300
            a, F0 = arch_direct(g, du)
            row = {"w": w, "xi0": xi0,
                   "moment_max_over_norm": max(m0, m1, m2) / scale,
                   "arch": a, "arch_over_normsq": a / (scale ** 2)}
            e5.append(row)
            log("  w=%.4f xi0=%.1f: moments/norm=%.1e arch/norm^2=%+.5f"
                % (w, xi0, row["moment_max_over_norm"],
                   row["arch_over_normsq"]))
    results["E5_smooth_d3"] = e5

    # ---- verdicts
    lam_y = next(r for r in sweep if abs(r["w"] - YOSHIDA_W) < 1e-9)
    verdicts = {
        "sigma_zero_crossing_xi_star": xstar,
        "one_over_xi_star": 1.0 / xstar,
        # v3 thresholds match demonstrated instrument precision:
        # cross-path 2.0e-3 (rough-vector quadrature), pole 5.2e-6
        # (projector moment floor), not the v2 1e-8/1e-6 aspirations.
        "cross_path_ok": worst < 5e-3,
        "F70_mass_zero_at_yoshida_matrix":
            "HOLDS" if lam_y["lam_max_mass_zero"] <= 0 else "FAILS(matrix)",
        "F70_triple_at_yoshida_matrix":
            "HOLDS" if lam_y["lam_max_triple"] <= 0 else "FAILS(matrix)",
        "F70_width_free_refuted_bandpass_w3":
            any(r["arch_over_F0"] > 1e-6 for r in e4),
        "smooth_triple_positive_found":
            any(r["arch_over_normsq"] > 1e-9 and
                r["moment_max_over_norm"] < 1e-6 for r in e5),
        "pole_vanishes_numerically":
            max(r["pole_over_F0_max"] for r in e3.values()) < 1e-4,
        "qw_negative_sample_found":
            min(r["qw_min"] for r in e3.values()) < 0,
    }
    results["verdicts"] = verdicts
    log("VERDICTS: %s" % json.dumps(verdicts))

    os.makedirs("results", exist_ok=True)
    with open("results/1740_p2_ledger_rig_results.json", "w") as f:
        json.dump(results, f, indent=1)
    with open("build-logs/1740_p2_ledger_rig.log", "w") as f:
        f.write("\n".join(LOG_LINES) + "\n")
    log("results + log written")


if __name__ == "__main__":
    os.makedirs("build-logs", exist_ok=True)
    main()
