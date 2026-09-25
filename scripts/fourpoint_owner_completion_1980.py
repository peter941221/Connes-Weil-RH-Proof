#!/usr/bin/env python3
# fourpoint_owner_completion_1980.py — record 1980 (map 106, pre-registered run)
#
# The pre-registered falsification run of docs/proofs/
# 1980_fourpoint_face_census_and_preregistration.md: the Cut-2 gate entries
# C = int K W, b = int K P W, D = int K P^2 W are measured on the COMPLETED
# healthy owner (real first zero, N = 0, routeNodes = empty) instead of the
# 8-node design representative of record 1959.
#
# Classification was committed BEFORE this run (commit 09d1f539) and applies
# to the default point (window scale 1.0, convolution count n = 0) only:
#
#   GO_CANDIDATE : C > 0 and D < 0, each sign margin > 3x its certified
#                  Ap/B spread (relative spread < 1/3 on C and on D).
#   PARK         : otherwise.
#
# Owner, coded verbatim from the committed definitions:
#
#   healthyCorrectionNodes rho N routeNodes
#     = sourceNontrivialZerosInClosedBallFinset rho (2^(N+1) + 2 + dist 2 rho)
#       union routeNodes union healthyUnscaledTargetNodes rho
#         [Dev/C1ExplicitHealthyCorrectionBudget.lean:34-42]
#   healthyUnscaledTargetNodes rho
#     = sourceFunctionalEquationOrbit rho union {rho+1/2, 1/2, 1, 3/2}
#         [Dev/C1HealthyYoshidaUnscaledOrbit.lean:31-33]
#   sourceFunctionalEquationOrbit rho = {rho, 1 - star rho, star rho, 1 - rho}
#         [Source/CC20YoshidaFullProduct.lean:52-53]
#   healthyUnscaledTargetValue: orbit priority (rho -> 1, 1 - star rho -> -1,
#   other orbit points -> 0), then -1 at rho + 1/2, else 0
#         [Dev/C1HealthyYoshidaUnscaledOrbit.lean:39-43]
#   base pins: laplaceAt base w = 1 on every owner node (hbaseTargets)
#         [Dev/C1HealthyYoshidaUnscaledOrbit.lean:544-547]
#
# On the critical line (rho = 1/2 + i gamma_1) the orbit collapses to the two
# distinct nodes {rho, 1 - rho}, so with N = 0 the owner has M = 10 nodes:
# rho (target 1), 1 - rho (target -1), rho + 1/2 (target -1), 1/2, 1, 3/2
# (targets 0), and the four closed-ball zero ordinates gamma_2..gamma_5
# (kill targets 0).  gamma_6 lies outside the ball (18.80 > 18.214) and is
# excluded, verified in code below.  The zero ordinates are external
# classical numerics used as node positions; the formal Finset stays
# abstract.
#
# Representative family (same architecture as record 1959 "design"): one
# Gevrey window per node,
#     f_j(x) = A_j phi(x; a_j, k) e^{i theta_j x},
#     phi(x; a, k) = exp(-k/(1 - (x/a)^2)) on |x| < a,   theta_j = -Im(node j),
# all ten widths distinct (a single width makes rows of the same height
# indistinguishable and the interpolation singular; law of record 1959
# section 1.2).  Two 10x10 solves: base targets all 1, correction targets
# healthyUnscaledTargetValue.
#
# Instruments reused from the certified record-1959 rig
# (scripts/fourpoint_owner_density_1959.py, which this file imports):
# Gauss quadrature, kernel/prime machinery (law F80 phase convention, law F81
# measure weights), certified route pair (Ap, B), the 1919 variance identity
# check, tail fractions, evenness.  No new numerics are invented here.
#
# Readings reported at every knob: pins, solve conditioning, W(0), peak,
# mass confinement, C, b, D, det, certified spreads, the 1919 identity,
# lam+ = (B' + sqrt(B'^2 - 4 C D)) / (2 C)  (positive whenever C > 0, D < 0),
# the Cut-1 window factor (K^4 + lam+)^2 / lam+^2 with K = 3 + |rho|,
# the required tail budget M_n (at smc = 1, shellStart = 0, xiMult = 1)
#     M_n^2 < xiMult lam^2 / (4 smc (3/4)^shellStart K^4 (K^4+lam)^2 (2 pi)^12)
# and the strip contraction T_need of the base.
#
# No gate sign is proved here; classification is per the pre-registration.

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_owner_density_1959 as r59  # noqa: E402  (certified machinery)

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------------------------ owner

GAMMA1 = 14.134725141734693790
GAMMAS = [14.134725141734693790, 21.022039638771554993,
          25.010857580145688763, 27.670321930357040,
          30.424876125859513210, 32.935061587739189691]


def ball_radius(rho, n_shell):
    """2^(N+1) + 2 + dist 2 rho  [C1ExplicitHealthyCorrectionBudget.lean:35]."""
    return 2.0 ** (n_shell + 1) + 2.0 + abs(2.0 - rho)


def kill_zeros(rho, n_shell):
    r = ball_radius(rho, n_shell)
    out = []
    for g in GAMMAS:
        z = 0.5 + 1j * g
        if abs(z - rho) <= r and abs(z - rho) > 1e-9:
            out.append(z)
    return out, r


def same(a, b):
    return abs(a - b) <= 1e-9


def owner_nodes(rho, n_shell):
    """healthyCorrectionNodes rho N empty, deduped with orbit priority."""
    orbit = [rho, 1 - np.conj(rho), np.conj(rho), 1 - rho]
    nodes, values = [], []

    def add(z, v):
        for i, t in enumerate(nodes):
            if same(t, z):
                return
        nodes.append(z)
        values.append(v)

    # orbit priority: rho -> 1, 1 - star rho -> -1, remaining orbit points 0
    add(rho, 1.0 + 0j)
    add(1 - np.conj(rho), -1.0 + 0j)
    add(np.conj(rho), 0j)
    add(1 - rho, 0j)
    add(rho + 0.5, -1.0 + 0j)
    add(0.5 + 0j, 0j)
    add(1.0 + 0j, 0j)
    add(1.5 + 0j, 0j)
    for z in kill_zeros(rho, n_shell)[0]:
        add(z, 0j)
    return nodes, values


def counterpart_nodes(rho):
    """Centered orbit nodes of the four-point annihilator (record 1918)."""
    return [rho - 0.5, (1 - np.conj(rho)) - 0.5,
            np.conj(rho) - 0.5, (1 - rho) - 0.5]


# ------------------------------------------------- family (generalized)

def family_for(nodes, scale):
    """(a_j, theta_j) per node; all widths distinct, theta_j = -Im(node j).

    Width groups by height: the three nodes at |Im| = gamma_1 need pairwise
    distinct widths (same-height rows are indistinguishable at equal width),
    the real-axis triple likewise, and each kill height gets its own width.
    """
    g1 = float(rho_g1.imag)
    plan = {}
    widths_h1 = [2.0, 2.4, 2.8]
    widths_real = [2.1, 2.5, 2.9]
    widths_kill = [2.2, 2.6, 3.0, 3.4]
    fam = []
    for z in nodes:
        iz = float(np.imag(z))
        if abs(iz - g1) < 1e-9 or abs(iz + g1) < 1e-9:
            key, pool = "h1", widths_h1
        elif abs(iz) < 1e-9:
            key, pool = "real", widths_real
        else:
            key, pool = "kill", widths_kill
        idx = plan.get(key, 0)
        plan[key] = idx + 1
        fam.append((scale * pool[min(idx, len(pool) - 1)], -iz))
    return fam


rho_g1 = 0.5 + 1j * GAMMA1


def family_quad(fam, k):
    return [r59.phi_weights(a, panels=6, m=400) for (a, _th) in fam]


def family_values(fam, k, s, XW):
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    V = np.empty((len(fam), s.shape[0]), dtype=complex)
    for j, (a, th) in enumerate(fam):
        V[j, :] = a * r59.phi_laplace(a, k, a * (s + 1j * th), XW=XW[j])
    return V


def interpolate(fam, k, XW, nodes, ys):
    M = family_values(fam, k, np.array(nodes, dtype=complex), XW).T
    cond = float(np.linalg.cond(M))
    A = np.linalg.solve(M, np.asarray(ys, dtype=complex))
    resid = float(np.max(np.abs(M @ A - np.asarray(ys, dtype=complex))))
    return A, {"cond": cond, "resid": resid,
               "max_A": float(np.max(np.abs(A)))}


def amplitudes(nodes, values, fam, k, XW):
    A_base, info_b = interpolate(fam, k, XW, nodes, np.ones(len(nodes)))
    A_corr, info_c = interpolate(fam, k, XW, nodes, values)
    return A_base, A_corr, {"base": info_b, "corr": info_c}


def owner_density(nodes, fam, k, n, xi, XW, A):
    """W(xi) = |L_base(1/2 - 2 pi i xi)|^(2(n+1)) |L_corr(1/2 - 2 pi i xi)|^2."""
    A_base, A_corr = A
    s = 0.5 - 2j * np.pi * np.asarray(xi)
    V = family_values(fam, k, s, XW)
    Lb = A_base @ V
    Lc = A_corr @ V
    W = np.abs(Lb) ** (2 * (n + 1)) * np.abs(Lc) ** 2
    term = np.abs(A_base[:, None] * V)
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(np.abs(Lb) > 0, term.max(axis=0) / np.abs(Lb),
                         np.inf)
    return W, Lb, Lc, ratio


def check_pins(nodes, values, fam, k, XW, A):
    A_base, A_corr = A
    out = []
    for z, y in zip(nodes, values):
        V = family_values(fam, k, np.array([z]), XW)[:, 0]
        Lb = complex(np.sum(A_base * V))
        Lc = complex(np.sum(A_corr * V))
        out.append({"node": [float(z.real), float(z.imag)],
                    "err_base": abs(Lb - 1.0), "err_corr": abs(Lc - y)})
    return out


def contraction_scan(nodes, fam, k, tmax, nt=400,
                     sigmas=(0.0, 0.25, 0.5, 0.75, 1.0), XW=None):
    A_base, _, _ = amplitudes(nodes, VALUES, fam, k, XW)
    ts = np.linspace(0.0, tmax, nt)
    prof = np.zeros(nt)
    for s0 in sigmas:
        grid = np.asarray(s0 + 1j * ts, dtype=complex)
        V = family_values(fam, k, grid, XW)
        prof = np.maximum(prof, np.abs(A_base @ V))
    T_need = None
    for i in range(nt):
        if prof[i:].max() <= 0.5:
            T_need = float(ts[i])
            break
    return {"T_need": T_need, "global_max": float(prof.max())}


VALUES = None  # set in run_case


# ------------------------------------------------------------- readings

def run_case(scale, n, k=30.0, xi_max=40.0, dxi=0.004):
    global VALUES
    rho = rho_g1
    gamma = GAMMA1
    tag = "owner sc=%.2f k=%.1f n=%d" % (scale, k, n)
    log("case %s" % tag)
    nodes, values = owner_nodes(rho, 0)
    VALUES = values
    kills, radius = kill_zeros(rho, 0)
    fam = family_for(nodes, scale)
    XW = family_quad(fam, k)
    A = amplitudes(nodes, values, fam, k, XW)
    pins = check_pins(nodes, values, fam, k, XW, (A[0], A[1]))
    pin_b = max(p["err_base"] for p in pins)
    pin_c = max(p["err_corr"] for p in pins)
    log("  M = %d nodes ; ball radius %.4f ; kill = %s"
        % (len(nodes), radius,
           ["%.4f" % z.imag for z in kills]))
    log("  pins: max |L_base-1| = %.2e ; max |L_corr-y| = %.2e ; cond %.2e"
        % (pin_b, pin_c, A[2]["base"]["cond"]))

    nxi = int(round(2.0 * xi_max / dxi)) + 1
    xi = np.linspace(-xi_max, xi_max, nxi)
    W, Lb, _Lc, ratio = owner_density(nodes, fam, k, n, xi, XW,
                                      (A[0], A[1]))
    P = np.real(r59.P_from_nodes(xi, counterpart_nodes(rho)))
    support_radius = max(a for a, _ in fam) * (n + 2)
    ge = r59.gate_entries(xi, W, P, support_radius)
    spread = r59.route_spread(ge)
    dxi_eff = float(xi[1] - xi[0])
    tot = float(np.sum(W) * dxi_eff)
    W0 = float(W[np.argmin(np.abs(xi))])
    xp = float(xi[np.argmax(W)])
    tail4 = r59.tail_fraction(xi, W, 4.0)[0]
    tail6 = r59.tail_fraction(xi, W, 6.0)[0]

    D, C, B01 = ge["D"], ge["C"], ge["B01"]
    det = D * C - B01 * B01
    disc = B01 * B01 - 4.0 * C * D
    lam_plus = ((B01 + math.sqrt(disc)) / (2.0 * C)) if (C > 0 and disc > 0) \
        else None
    K = 3.0 + abs(rho)
    window = ((K ** 4 + abs(lam_plus)) ** 2 / lam_plus ** 2) \
        if lam_plus else None
    # required tail budget at smc = 1, shellStart = 0, xiMult = 1
    m_thr = None
    if lam_plus:
        denom = 4.0 * 1.0 * 1.0 * K ** 4 * (K ** 4 + abs(lam_plus)) ** 2 \
            * (2.0 * math.pi) ** 12
        m_thr = math.sqrt(max(1.0 * lam_plus ** 2 / denom, 0.0))

    cont = contraction_scan(nodes, fam, k, 80.0, XW=XW)
    vc = r59.variance_check(ge["mu"], P, xi, 0.0, gamma) if "mu" in ge \
        else None

    rec = {
        "tag": tag, "scale": scale, "n": n, "k": k,
        "rho": [rho.real, rho.imag], "M": len(nodes),
        "ball_radius": radius,
        "kill_imag": [float(z.imag) for z in kills],
        "nodes": [[float(z.real), float(z.imag)] for z in nodes],
        "values": [[float(v.real), float(v.imag)] for v in values],
        "family": [[float(a), float(th)] for a, th in fam],
        "pin_err_base": pin_b, "pin_err_corr": pin_c, "solve": A[2],
        "cancel_ratio_max": float(np.max(ratio[np.abs(Lb) > 0])),
        "W0": W0, "xi_peak": xp, "mass": tot,
        "tail_gt4": tail4, "tail_gt6": tail6,
        "evenness_defect": r59.evenness(W, xi),
        "support_radius": support_radius, "n_primes": ge["n_primes"],
        "arch_C": ge["arch"][0], "arch_B01": ge["arch"][1],
        "arch_D": ge["arch"][2],
        "prime_C": ge["prime"][ge["route_key"]][0],
        "prime_B01": ge["prime"][ge["route_key"]][1],
        "prime_D": ge["prime"][ge["route_key"]][2],
        "C": C, "B01": B01, "D": D, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "routes": sorted(ge["prime"].keys()),
        "variance_check": vc,
        "lam_plus": lam_plus, "window_factor": window, "Mn_threshold": m_thr,
        "K4": K ** 4,
        "contraction_T_need": cont["T_need"],
        "contraction_max": cont["global_max"],
    }
    log("  W(0) = %.2e ; peak |xi| = %+.4f ; tail>4 = %.2e ; tail>6 = %.2e"
        % (W0, xp, tail4, tail6))
    log("  full   C=%+.6e b=%+.6e D=%+.6e det=%+.6e" % (C, B01, D, det))
    log("  spread (rel): C %.1e b %.1e D %.1e  [routes %s]"
        % (spread[0], spread[1], spread[2], ",".join(rec["routes"])))
    if vc:
        d1 = abs(vc["det_var"] - det) / max(abs(det), 1e-300)
        d2 = abs(vc["det_moment"] - det) / max(abs(det), 1e-300)
        log("  1919 identity: det_var rel %.1e ; det_moment rel %.1e"
            % (d1, d2))
    if lam_plus:
        log("  lam+ = %.6e ; window factor %.3f ; Mn threshold %.3e"
            % (lam_plus, window, m_thr))
    log("  contraction: max|L_base| %.3e ; T_need = %s"
        % (cont["global_max"], str(cont["T_need"])))
    return rec


def classify(rec):
    """Pre-registered rule (commit 09d1f539), default point only."""
    ok_c = rec["C"] > 0.0 and rec["spread_C"] < 1.0 / 3.0
    ok_d = rec["D"] < 0.0 and rec["spread_D"] < 1.0 / 3.0
    return "GO_CANDIDATE" if (ok_c and ok_d) else "PARK"


def main():
    quick = "--quick" in sys.argv
    xi_max, dxi = (8.0, 0.008) if quick else (40.0, 0.004)
    knobs = [(1.0, 0)] if quick else \
        [(1.0, 0), (0.9, 0), (1.1, 0), (1.0, 1)]
    rows = []
    for scale, n in knobs:
        rows.append(run_case(scale, n, xi_max=xi_max, dxi=dxi))
    default = next(r for r in rows if r["scale"] == 1.0 and r["n"] == 0)
    verdict = classify(default) if not quick else "QUICK_SMOKE"
    report = {
        "record": 1980,
        "status": "PREFLIGHT_RUN",
        "pre_registration_commit": "09d1f539",
        "owner": "healthyCorrectionNodes rho_1 0 empty (M = %d)" % default["M"],
        "xi_max": xi_max, "dxi": dxi,
        "classification_rule": (
            "C > 0 and D < 0 with relative certified spread < 1/3 on each"),
        "verdict": verdict,
        "cases": rows,
    }
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "1980_owner_completion.json")
    with open(out, "w", encoding="utf-8") as stream:
        stream.write(json.dumps(report, indent=2) + "\n")
    log("verdict (default point sc=1.0 n=0): %s" % verdict)
    log("wrote %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()
