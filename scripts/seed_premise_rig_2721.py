#!/usr/bin/env python3
r"""Record 2721 (G1 swing 2c): analytic replacement of the 2718 seed premise.

Task card (bounded-progress gate):
  consumer   riemannHypothesis_of_four_point_span_contradiction_producer,
             unchanged -- this record strengthens the ERROR LEDGER under the
             same four sign claims certified at record 2718 (model grade)
  owner      the stored record-1980 trial-owner models at
             (gamma_1, N=4, n=3) and (gamma_2, N=5, n=3); node constants are
             the stored floats, taken as the owner definition
  premise    2718 carried two observational premises:
             E_seed = 10 x observed GL-600-vs-GL-1200 spread, and
             M_grid = 10 x observed 0.02-vs-0.01 channel movement
  criterion  per sign claim: slack > 0 at
             E_seed_analytic = D_float + 10 Lmax^9 B_tail (triangle
             inequality; every leg computed or certified in-run) and at
             M_grid_ladder = m(0.02,0.01) + (1+GEO_TAIL) m(0.01,0.005);
             the same-run reprice must reproduce the committed 2718 rows
  budget     one rig run: both candidates, grids 0.02/0.01/0.005, seed
             orders 300/600/1200 at the claim points, pole scan k <= 3199,
             a-ladder {0.06,0.04,0.03,0.02}
  stop       verdict recorded; a RED claim or anchor failure is a finding
             and triggers environment diagnosis, never producer patching

Method -- the seed premise becomes analytic by a split-rule bridge (the
record-2057 law: bound the DIFFERENCE between rules, computed, then bound
each piece analytically):

  |L_300(u) - L_ideal(u)| <= |L_300 - L_1200|            (D_float, in-run)
                           + |L_1200 - L_ideal|           (B_tail, below)
  L = L1^10, |a^10 - b^10| <= 10 max(a,b)^9 |a-b|; f <= 1 pointwise, so
  |L1(u)| <= int e^{0.5 Re(u) x} dx = 2 sinh(2r)/r, r = 0.5 |Re u| (the
  node sets include mirror nodes, measured max |Re u| = 1 -> 4.70).

  For one u, F(x) = f(x) e^{0.5 u x} on [-2,2], f = T(x+2)T(2-x) even,
  T = 1/(1+exp(1/y - 1/(1-y))) flat at y in {0,1}.  Poles of T in y solve
  g(y) = i pi (2k+1):  c y^2 - (c+2) y + 1 = 0, c = i pi(2k+1); they hug
  the corners y in {0,1} like (1/sigma^2, 1/sigma), so poles ACCUMULATE at
  the interval endpoints x in {-2,-1,1,2}: no whole-interval strip bound
  exists.  Cut at a: middle M_a = [-1-a, 1+a] (f = 1+delta, |delta| <=
  3 e^{-1/a}), panels [1+a, 2-a] and mirror (poles at distance d_min(a)),
  outer slabs |f| <= e^{-1/a}.

  |GL_1200(F) - I(F)| <= D_split(u)                        [computed]
                       + STRIP_M                           [entire, b-ladder]
                       + STRIP_pL + STRIP_pR               [poles at d_min/2]
                       + SMALL_mass(a)                     [delta + slabs]
  D_split(u) = |GL_[−2,2](F) − S(u)| with S = GL on M_a of e^{0.5ux} plus
  fresh GL rules on the two panels of F (float rounding charged), so
  |GL − I| <= |GL − S| + |S − I| and |S − I| is bounded by the three strip
  terms plus the small-mass charge.  The a-ladder min is taken (every
  branch sound).

  Grid premise: narrowed, not eliminated.  mv_new = m(0.02,0.01) +
  (1 + GEO_TAIL) m(0.01,0.005) with GEO_TAIL = 1 the named ratio-2 tail
  premise (h^2 evidence: measured rung ratios per channel), replacing the
  old 10x two-grid inflation.  A fully analytic e(0.005) is NOT attempted:
  the prime channel is oscillatory and the EM absolute-mass route is
  vacuous (kp'' random-walk mass ~1e6 x the measured movements) -- the
  record-2278/2279 cancellation-floor class.

Certified object: the pipeline AS CODE on the stored float node constants
(model grade), same as 2718; the upgrade is on the error-ledger side.
Not certified here: complete owner (G2), decay constants (2720 covers P3),
shell identification (P4), map-103 reopening, producer GO, SourceRH, RH.

Run under WSL python3 (the 2718/2032 artifact era is WSL-python; the
record-2j law forbids cross-environment bitwise claims).
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op      # noqa: E402
import fourpoint_coupling_scan_2028 as scan   # noqa: E402
import fourpoint_diagonal_sign_1918 as rig    # noqa: E402
import fourpoint_owner_density_1959 as legacy  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402
import g1_joint_acceptance_repricing_2716 as r16  # noqa: E402

SRC32 = ROOT / "results/2032_gate_row_search.json"
SRC18 = ROOT / "results/2718_gate_sign_rig.json"
DXI_PRIMARY = 0.02
DXI_FINE = 0.01
DXI_TAIL = 0.005
XI_MAX = 25.0
SEED_ORDER = 300
SEED_ORDERS_STUDY = (600, 1200)
U = 2.0 ** -53
CANDIDATES = [(14.134725141734693, 4), (21.022039638771556, 5)]
E_SEED_INFLATION = 10.0
GRID_INFLATION = 10.0
GEO_TAIL = 1.0
A_LADDER = (0.06, 0.04, 0.03, 0.02)
MID_B_LADDER = (0.2, 0.5, 1.0, 1.6, 2.4, 3.2)
K_POLE_MAX = 3200
SMOKE = "--smoke" in sys.argv
SEED0_EXACT = 59049.0          # laplaceAt(smoothSeed, 0) = 3 exactly -> 3^10
T0 = time.time()

if SMOKE:
    CANDIDATES = CANDIDATES[:1]
    K_POLE_MAX = 400
    MID_B_LADDER = (0.5, 1.5)


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def grid_of(dxi):
    return np.arange(-XI_MAX, XI_MAX + 0.5 * dxi, dxi)


def rebuild_row(rho, N, n, dxi, seed_transform, seed0):
    """The record-2032 call order, verbatim, for one (rho, N, n, dxi)."""
    owner, targets, radius, known = op.build_owner(rho, N)
    values = [op.target_value(rho, z) for z in owner]
    xi = grid_of(dxi)
    centered_orbit = [z - 0.5 for z in op.healthy_targets(rho)[:4]]
    P = np.real(legacy.P_from_nodes(xi, centered_orbit))
    W = scan.build_density(xi, seed_transform, seed0, owner, targets,
                           values, n)
    axis = 0.5 - 2j * math.pi * xi
    lb = op.cardinal_transform(targets, [1.0 + 0j] * len(targets), seed0,
                               axis, seed_transform)
    lc = op.cardinal_transform(owner, values, seed0, axis, seed_transform)
    W_direct = np.abs(lb) ** (2 * (n + 1)) * np.abs(lc) ** 2
    vals, logs = scan.fast_prime_powers_up_to(math.exp(2.0 * (n + 2)))
    kp = scan.direct_prime_channel(xi, vals, logs)
    sig = rig.sigma_vec(2.0 * math.pi * xi)
    fs = (W, P * W, P * P * W)
    arch = [float(np.trapezoid(sig * f, xi)) for f in fs]
    pr = [float(np.trapezoid(kp * f, xi)) for f in fs]
    C = arch[0] + pr[0]
    b = arch[1] + pr[1]
    D = arch[2] + pr[2]
    det = C * D - b * b
    lam = (b / C) if C else float("nan")
    return {
        "xi": xi, "P": P, "W": W, "W_direct": W_direct, "lb": lb, "lc": lc,
        "owner": owner, "targets": targets, "radius": radius,
        "known_count": len(known), "kp": kp, "prime_count": int(vals.size),
        "vals": vals, "logs": logs, "sig": sig,
        "gate": {"arch": arch, "pr": pr, "C": C, "b": b, "D": D, "det": det,
                 "lambda": lam},
    }


def sigma_reference(xi):
    """mpmath digamma reference at dps 35 -> exact per-node sigma."""
    with mp.workdps(35):
        out = np.empty(xi.size, dtype=float)
        for i, x in enumerate(xi):
            z = mp.mpc(0.25, -0.5 * (2.0 * math.pi * float(x)))
            out[i] = float(mp.log(mp.pi) - mp.re(mp.digamma(z)))
    return out


def cardinal_sensitivity(nodes, values, seed0, xi, seed_transform):
    """S(s): |dlb(s)| <= E_L * S(s) under a uniform seed error E_L."""
    s_axis = 0.5 - 2j * math.pi * xi
    S = np.zeros(xi.size, dtype=float)
    detail = []
    for z, v in zip(nodes, values):
        if abs(v) == 0:
            continue
        denom = op.node_product(nodes, z, z) * seed0
        c = v / denom
        Q = op.node_product(nodes, z, s_axis)
        L = seed_transform(s_axis - z)
        S += np.abs(c) * np.abs(Q) * (1.0 + np.abs(L) / abs(seed0))
        detail.append({"z": [float(z.real), float(z.imag)],
                       "abs_c": float(abs(c)),
                       "max_abs_Q": float(np.max(np.abs(Q))),
                       "max_abs_L": float(np.max(np.abs(L)))})
    return S, detail


# ------------------------------------------------------------------ poles --
def pole_panel_distance(a: float):
    """d_min from the upper-half-plane logistic poles to the segment [a, 1-a].

    g(y) = 1/y - 1/(1-y) = i pi (2k+1)  <=>  c y^2 - (c+2) y + 1 = 0 with
    c = i pi (2k+1).  F is real on the real axis, so poles come in
    conjugate pairs; keep the upper-plane member (conj of a lower root).
    """
    with mp.workdps(60):
        dmin = mp.inf
        binder = None
        for k in range(K_POLE_MAX):
            c = 1j * mp.pi * (2 * k + 1)
            disc = (c + 2) ** 2 - 4 * c
            sq = mp.sqrt(disc)
            for r in ((c + 2 + sq) / (2 * c), (c + 2 - sq) / (2 * c)):
                ru = mp.conj(r) if mp.im(r) < 0 else r
                if mp.im(ru) <= 0:
                    continue
                x, h = float(mp.re(ru)), float(mp.im(ru))
                dx = 0.0 if a <= x <= 1 - a else min(abs(x - a),
                                                     abs(x - (1 - a)))
                d = math.hypot(dx, h)
                if d < dmin:
                    dmin = d
                    binder = (k, x, h)
    return float(dmin), binder


def panel_strip_bound(a: float, dmin: float, smax: float, remax: float,
                      m: int):
    """Trefethen strip bound for a fresh m-node GL rule on ONE x-panel.

    x-panel [1+a, 2-a] (mirror symmetric); half-length c_p = (1-2a)/2,
    strip half-height b_p = dmin/2.  M = sup on the ellipse boundary of
    |f(x)| (sampled at 240 mpmath points) times the analytic e^{0.5ux}
    factor at the strip edge.
    """
    c_p = (1.0 - 2 * a) / 2.0
    b_p = dmin / 2.0
    ratio = b_p / c_p
    rho = ratio + math.sqrt(1 + ratio * ratio)
    sup_f = 0.0
    with mp.workdps(40):
        mid = 1.5
        for th in np.linspace(0, 2 * math.pi, 240, endpoint=False):
            xr = mid + c_p * math.cos(th)
            xi_ = b_p * math.sin(th)
            y1 = mp.mpc(xr + 2, xi_)
            y2 = mp.mpc(2 - xr, -xi_)
            t1 = 1 / (1 + mp.exp(1 / y1 - 1 / (1 - y1)))
            t2 = 1 / (1 + mp.exp(1 / y2 - 1 / (1 - y2)))
            sup_f = max(sup_f, float(abs(t1 * t2)))
    M = sup_f * math.exp(0.5 * smax * b_p + remax)
    return 4.0 * M * rho ** (-2 * m) / (1.0 - rho ** (-2)), rho, M


def middle_strip_bound(a: float, smax: float, remax: float, m: int):
    """Strip bound for the fresh m-node GL rule of e^{0.5ux} on M_a.

    Entire integrand: every strip height is valid; min over a b-ladder.
    """
    c_m = 1.0 + a
    best = math.inf
    best_b = None
    for b in MID_B_LADDER:
        ratio = b / c_m
        rho = ratio + math.sqrt(1 + ratio * ratio)
        M = math.exp(0.5 * smax * b + 0.5 * remax * c_m)
        est = 4.0 * M * rho ** (-2 * m) / (1.0 - rho ** (-2))
        if est < best:
            best, best_b = est, b
    return best, best_b


def small_mass(a: float, remax: float):
    """Mass charge for delta on M_a plus the two outer slabs (I and GL)."""
    e_small = math.exp(-1.0 / a) * math.exp(remax)
    return (2.0 + 2.0 * a) * 3.0 * e_small + (2.0 * a + 4.0) * e_small


def make_raw_l1(order: int):
    """Pre-power L1 evaluator mirroring make_powered_seed verbatim.

    Same node/weight construction and the same 600-element chunk/sum order
    as the factory, minus the SEED_POWER exponent; asserted bitwise against
    the factory transform at probe points in main().
    """
    nodes, weights = np.polynomial.legendre.leggauss(order)
    x = 2.0 * nodes
    w = 2.0 * weights * op.smooth_seed_raw(x)
    scale = powered.SEED_SCALE

    def raw(s):
        values = np.asarray(s, dtype=complex)
        flat = values.reshape(-1)
        out = np.empty_like(flat)
        for start in range(0, flat.size, 600):
            block = flat[start:start + 600]
            out[start:start + 600] = np.sum(
                np.exp((scale * block)[:, None] * x[None, :]) * w[None, :],
                axis=1)
        return out.reshape(values.shape)

    return raw


def sub_rule(m: int, lo: float, hi: float):
    """Fresh m-node GL nodes/weights on [lo, hi] and f at the nodes."""
    g, wg = np.polynomial.legendre.leggauss(m)
    half = 0.5 * (hi - lo)
    x = (0.5 * (lo + hi)) + half * g
    w = half * wg
    return x, w


def d_split_leg(pts_list, a: float, m: int, l_raw):
    """max_u |GL(F) - S(u)| + rounding; S = M_a-rule + 2 panel rules.

    pts_list: list of complex arrays (the claim evaluation points).
    l_raw: the pre-power L1 evaluator at order m (the GL(F) side).
    Returns (d_split_max, round_allow, n_pts).
    """
    xM, wM = sub_rule(m, -1 - a, 1 + a)
    xL, wL = sub_rule(m, -2 + a, -1 - a)
    xR, wR = sub_rule(m, 1 + a, 2 - a)
    fM = wM * op.smooth_seed_raw(xM)
    fL = wL * op.smooth_seed_raw(xL)
    fR = wR * op.smooth_seed_raw(xR)
    d_max = 0.0
    r_max = 0.0
    n = 0
    for arr in pts_list:
        for i0 in range(0, arr.size, 2000):
            u = arr[i0:i0 + 2000]
            gl = l_raw(u)
            sM = np.sum(np.exp(0.5 * np.outer(u, xM)) * fM, axis=1)
            sL = np.sum(np.exp(0.5 * np.outer(u, xL)) * fL, axis=1)
            sR = np.sum(np.exp(0.5 * np.outer(u, xR)) * fR, axis=1)
            S = sM + sL + sR
            d_max = max(d_max, float(np.max(np.abs(gl - S))))
            r_max = max(r_max, float(np.max(np.abs(gl)))
                        + float(np.max(np.abs(S))))
            n += u.size
    return d_max, 64.0 * U * r_max, n


def main() -> None:
    d32 = json.loads(SRC32.read_text())
    idx32 = {(r["gamma"], r["N"], r["n"]): r for r in d32["rows"]}
    d18 = json.loads(SRC18.read_text())
    idx18 = {(r["gamma"], r["N"]): r for r in d18["rows"]}

    seed_transform = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])

    # ------------------------------------------------ anchor a3: seed0 ---
    d81 = json.loads(
        (ROOT / "results/1981_powered_seed_underapprox.json").read_text())
    s0_ref = d81["seed"]["laplace_at_zero"]
    assert [seed0.real, seed0.imag] == s0_ref, (seed0, s0_ref)
    log("anchor a3 OK: seed0 bitwise == committed 1981 laplace_at_zero")
    a4 = abs(seed0 - SEED0_EXACT)
    log("anchor a4: |L300(0) - 3^10| = %.4e" % a4)

    # raw L1 (pre-power) mirror at order 1200, asserted bitwise against the
    # factory transform (same chunk/sum order, exponent removed)
    l_raw1200 = make_raw_l1(1200)
    probe = np.array([0j, 1j * 3.0, -40.0 + 2j * 91.0, 0.5 + 2j * 157.0])
    fac = powered.make_powered_seed(order=1200)(probe)
    mir = l_raw1200(probe) ** powered.SEED_POWER
    assert np.array_equal(fac, mir), (fac, mir)
    log("anchor a6 OK: raw-L1 mirror bitwise == factory 1200 transform")

    results = []
    for gamma, N in CANDIDATES:
        rho = complex(0.55, gamma)
        row32 = idx32[(gamma, N, 3)]
        blk = {"gamma": gamma, "N": N, "n": 3,
               "owner_cardinality": row32["owner_cardinality"],
               "known_zero_count": row32["known_zero_count"],
               "radius": row32["radius"]}

        # --------------------------------------- anchor a1: bitwise row ---
        bad = []
        rebuild = {}
        for dxi, tag in ((DXI_PRIMARY, "dxi0.02"), (DXI_FINE, "dxi0.01"),
                         (DXI_TAIL, "dxi0.005")):
            d = rebuild_row(rho, N, 3, dxi, seed_transform, seed0)
            rebuild[tag] = d
            assert float(np.max(np.abs(d["W"] - d["W_direct"]))) == 0.0
            if tag not in row32:
                continue
            ref = row32[tag]
            g = d["gate"]
            for name, got, want in (("C", g["C"], ref["C"]),
                                    ("b", g["b"], ref["b"]),
                                    ("D", g["D"], ref["D"]),
                                    ("det", g["det"], ref["det"]),
                                    ("lambda", g["lambda"], ref["lambda"]),
                                    ("arch0", g["arch"][0], ref["arch"][0]),
                                    ("arch1", g["arch"][1], ref["arch"][1]),
                                    ("arch2", g["arch"][2], ref["arch"][2])):
                if got != want:
                    bad.append((tag, name, got, want))
        blk["anchor_bitwise_mismatches"] = len(bad)
        if bad:
            blk["anchor_detail"] = [list(x) for x in bad[:12]]
            log("ANCHOR FAIL at (%g, %d): %d mismatches" % (gamma, N, len(bad)))
            results.append(blk)
            continue
        log("anchor a1 OK: (%g, N=%d) bitwise vs stored rows, three grids"
            % (gamma, N))

        # --------------------------------------------- shadow rig (.02) ---
        d = rebuild["dxi0.02"]
        xi, W, P, kp, sig = d["xi"], d["W"], d["P"], d["kp"], d["sig"]
        lb, lc = d["lb"], d["lc"]
        gate = d["gate"]
        C, b, D, det = gate["C"], gate["b"], gate["D"], gate["det"]

        sig_ref = sigma_reference(xi)
        dsig_abs = np.abs(sig - sig_ref)
        wsum = float(np.sum(2.0 * d["logs"] / np.sqrt(d["vals"].astype(float))))

        Sb, det_b = cardinal_sensitivity(
            d["targets"], [1.0 + 0j] * len(d["targets"]), seed0, xi,
            seed_transform)
        Sc, det_c = cardinal_sensitivity(
            d["owner"], [op.target_value(rho, z) for z in d["owner"]],
            seed0, xi, seed_transform)
        G = (8.0 * np.abs(lb) ** 7 * np.abs(lc) ** 2 * Sb
             + 2.0 * np.abs(lb) ** 8 * np.abs(lc) * Sc)

        wvec = (np.ones_like(P), np.abs(P), P * P)
        g_abs = np.abs(sig) + np.abs(kp)
        chan = []
        for wv in wvec:
            fi = wv * W
            A_seed = float(np.trapezoid(g_abs * wv * G, xi))
            R_sigma = float(np.trapezoid(dsig_abs * wv * W, xi))
            R_sigfl = float(np.trapezoid(4.0 * U * np.abs(sig) * wv * W, xi))
            R_trap_a = 16.0 * U * float(np.trapezoid(np.abs(sig * fi), xi))
            R_cos = 1e-12 * wsum * float(np.trapezoid(fi, xi))
            R_trap_p = 16.0 * U * float(np.trapezoid(np.abs(kp * fi), xi))
            R_float = 1e-11 * float(np.trapezoid(g_abs * fi, xi))
            chan.append({
                "A_seed": A_seed,
                "nonseed": R_sigma + R_sigfl + R_trap_a + R_cos
                           + R_trap_p + R_float,
                "parts": {"R_sigma": R_sigma, "R_sigfl": R_sigfl,
                          "R_trap_arch": R_trap_a, "R_cos": R_cos,
                          "R_trap_pr": R_trap_p, "R_float": R_float},
            })
        A_det = (abs(D) * chan[0]["A_seed"] + abs(C) * chan[2]["A_seed"]
                 + 2.0 * abs(b) * chan[1]["A_seed"])
        ns_det = (abs(D) * chan[0]["nonseed"] + abs(C) * chan[2]["nonseed"]
                  + 2.0 * abs(b) * chan[1]["nonseed"] + 6.0 * U * abs(C * D))
        chan_det = {"A_seed": A_det, "nonseed": ns_det}

        # --------------------------------- seed study + evaluation class --
        s_axis = 0.5 - 2j * math.pi * xi
        pts = [s_axis - z for z in d["targets"]]
        pts += [s_axis - z for z, v in
                zip(d["owner"], [op.target_value(rho, z)
                                 for z in d["owner"]]) if abs(v) != 0]
        Ls = {SEED_ORDER: seed_transform}
        for o in SEED_ORDERS_STUDY:
            Ls[o] = powered.make_powered_seed(order=o)
        spread = {}
        for o in SEED_ORDERS_STUDY:
            m = 0.0
            for p in pts:
                m = max(m, float(np.max(np.abs(Ls[o](p) - Ls[300](p)))))
            m0 = abs(complex(Ls[o](np.array([0j]))[0]) - seed0)
            spread[str(o)] = {"max_abs_diff_vs_300": m, "abs_diff_at_0": m0}
            log("seed order %d vs 300: max|dL| = %.3e (at 0: %.3e)"
                % (o, m, m0))
        E_obs = spread[str(SEED_ORDERS_STUDY[-1])]["max_abs_diff_vs_300"]
        E_seed_old = E_SEED_INFLATION * E_obs

        # evaluation class for the analytic tail
        allpts = np.concatenate(pts + [np.array([0j])])
        smax_meas = float(np.max(np.abs(np.imag(allpts))))
        remax = float(np.max(np.abs(np.real(allpts))))
        smax = smax_meas + 1.0
        blk["eval_class"] = {"n_pts": int(allpts.size),
                             "smax_meas": smax_meas, "smax_charged": smax,
                             "remax": remax}
        log("eval class: %d pts, smax=%.2f (charged %.2f), remax=%.4f"
            % (allpts.size, smax_meas, smax, remax))

        # ------------------------------------- analytic tail (a-ladder) ---
        tail_table = []
        for a in A_LADDER:
            dmin, binder = pole_panel_distance(a)
            strip_p, rho_p, M_p = panel_strip_bound(a, dmin, smax, remax, 1200)
            strip_m, b_m = middle_strip_bound(a, smax, remax, 1200)
            smallm = small_mass(a, remax)
            d_sp, round_al, n_ds = d_split_leg(pts, a, 1200, l_raw1200)
            b_tail = d_sp + round_al + strip_m + 2 * strip_p + smallm
            tail_table.append({
                "a": a, "d_min": dmin, "binder_pole": binder,
                "panel_rho": rho_p, "panel_M": M_p, "panel_strip": strip_p,
                "middle_strip": strip_m, "middle_b": b_m,
                "small_mass": smallm, "d_split": d_sp, "n_d_split_pts": n_ds,
                "round_allow": round_al, "B_tail": b_tail,
            })
            log("a=%.2f: d_min=%.4f panel_strip=%.2e mid=%.2e small=%.2e "
                "d_split=%.2e -> B_tail=%.3e"
                % (a, dmin, strip_p, strip_m, smallm, d_sp, b_tail))
        best = min(tail_table, key=lambda r: r["B_tail"])
        B_tail = best["B_tail"]
        # f <= 1 pointwise (T in [0,1]) -> |L1(u)| <= int e^{0.5 Re(u) x}
        #                                   = 2 sinh(2r)/r, r = 0.5|Re u|
        rmax = 0.5 * remax
        L1_sup = (4.0 if rmax < 1e-9 else 2.0 * math.sinh(2.0 * rmax) / rmax)
        Lmax = L1_sup + B_tail
        B_seed_cert = E_obs + 10.0 * Lmax ** 9 * B_tail
        blk["analytic_seed"] = {
            "D_float": E_obs, "B_tail_best": B_tail, "a_best": best["a"],
            "L1_sup": L1_sup, "Lmax": Lmax, "B_seed_cert": B_seed_cert,
            "amplification": 10.0 * Lmax ** 9,
            "table": tail_table,
            "seed0_gap_within_B": bool(a4 <= B_seed_cert),
        }
        log("B_seed_cert = %.4e (D_float %.2e + tail %.2e; a*=%.2f, "
            "L1_sup=%.3f)" % (B_seed_cert, E_obs, 10.0 * Lmax ** 9 * B_tail,
                              best["a"], L1_sup))

        # ------------------------------------------ grid ladder (.005) ---
        gF = rebuild["dxi0.01"]["gate"]
        gT = rebuild["dxi0.005"]["gate"]
        d_arch = [abs(gate["arch"][i] - gF["arch"][i]) for i in range(3)]
        d_pr = [abs(gate["pr"][i] - gF["pr"][i]) for i in range(3)]
        m02 = [d_arch[i] + d_pr[i] for i in range(3)]
        d_arch2 = [abs(gF["arch"][i] - gT["arch"][i]) for i in range(3)]
        d_pr2 = [abs(gF["pr"][i] - gT["pr"][i]) for i in range(3)]
        m015 = [d_arch2[i] + d_pr2[i] for i in range(3)]
        M_ch_old = [GRID_INFLATION * m02[i] for i in range(3)]
        M_det_old = (abs(D) * M_ch_old[0] + abs(C) * M_ch_old[2]
                     + 2.0 * abs(b) * M_ch_old[1])
        M_ch = [m02[i] + (1.0 + GEO_TAIL) * m015[i] for i in range(3)]
        M_det = (abs(D) * M_ch[0] + abs(C) * M_ch[2] + 2.0 * abs(b) * M_ch[1])
        rung_ratio = [(m02[i] / m015[i] if m015[i] > 0 else None)
                      for i in range(3)]
        blk["grid_ladder"] = {
            "m_02_01": m02, "m_01_005": m015, "rung_ratio": rung_ratio,
            "geo_tail": GEO_TAIL, "M_ch_new": M_ch, "M_det_new": M_det,
            "M_ch_old": M_ch_old, "M_det_old": M_det_old,
            "rung_note": "measured ratios >> 4 mean the 0.005 rung sits at "
                         "or near the pipeline float floor (geometric "
                         "regime: nearest digamma pole |Im xi| ~ 0.0796, "
                         "h << pi*d); the named premise e(0.005) <= m015 "
                         "is charged at that scale with the measured "
                         "collapse as its evidence",
        }
        log("grid ladder: ratios %s mv_new %s (old %s)"
            % (["%.2f" % r for r in rung_ratio],
               ["%.3e" % x for x in M_ch], ["%.3e" % x for x in M_ch_old]))

        # ------------------------------------------------ claims ----------
        claims = []
        for name, margin, ch, mv_old, mv_new in (
                ("C_negative", abs(C), chan[0], M_ch_old[0], M_ch[0]),
                ("det_sign", abs(det), chan_det, M_det_old, M_det)):
            total_old = ch["nonseed"] + ch["A_seed"] * E_seed_old + mv_old
            total_new = ch["nonseed"] + ch["A_seed"] * B_seed_cert + mv_new
            e_crit_new = ((margin - ch["nonseed"] - mv_new) / ch["A_seed"]
                          if ch["A_seed"] > 0 else None)
            claims.append({
                "claim": name, "value": margin,
                "nonseed_allowance": ch["nonseed"],
                "A_seed": ch["A_seed"],
                "total_old": total_old, "slack_old": margin - total_old,
                "E_seed_old": E_seed_old, "mv_old": mv_old,
                "E_seed_new": B_seed_cert, "mv_new": mv_new,
                "total_new": total_new, "slack_new": margin - total_new,
                "E_L_critical_new": (float(e_crit_new)
                                     if e_crit_new is not None else None),
                "GREEN_old": bool(margin - total_old > 0),
                "GREEN_new": bool(margin - total_new > 0),
                "margin_ratio_new": (margin / total_new
                                     if total_new > 0 else None),
            })
        blk["claims"] = claims

        # ---------------------- branch robustness at the new allowances ---
        kind_c, _ = r16.gate_branches(C, b, det)
        dC = chan[0]["nonseed"] + chan[0]["A_seed"] * B_seed_cert + M_ch[0]
        db = chan[1]["nonseed"] + chan[1]["A_seed"] * B_seed_cert + M_ch[1]
        ddet = chan_det["nonseed"] + chan_det["A_seed"] * B_seed_cert + M_det
        branch_set = set()
        lplus = []
        for sc in (-1, 1):
            for sb in (-1, 1):
                for sd in (-1, 1):
                    kind, gd = r16.gate_branches(C + sc * dC, b + sb * db,
                                                 det + sd * ddet)
                    branch_set.add(kind)
                    if "Lplus" in gd:
                        lplus.append(float(gd["Lplus"]))
        blk.update({
            "sigma_max_delta": float(dsig_abs.max()),
            "prime_weight_sum": wsum,
            "seed_terms_base": det_b, "seed_terms_corr": det_c,
            "G_max": float(np.max(G)),
            "channels": chan, "channel_det": chan_det,
            "seed_study": spread,
            "E_seed_obs": E_obs, "E_seed_old_premise": E_seed_old,
            "seed0_exact_gap": a4,
            "branch_center": kind_c,
            "branch_corner_set": sorted(branch_set),
            "branch_robust": bool(branch_set == {kind_c}),
            "Lplus_corner_range": ([min(lplus), max(lplus)]
                                   if lplus else None),
            "gate": gate,
        })

        # ------------------------- same-run reprice vs committed 2718 -----
        r18 = idx18[(gamma, N)]
        drift = []
        for key, got, want in (
                ("E_seed_obs", E_obs, r18["E_seed_obs"]),
                ("E_seed_premise", E_seed_old, r18["E_seed_premise"]),
                ("M_ch0_old", M_ch_old[0], r18["grid_movement_channels"][0]),
                ("M_ch1_old", M_ch_old[1], r18["grid_movement_channels"][1]),
                ("M_ch2_old", M_ch_old[2], r18["grid_movement_channels"][2]),
                ("M_det_old", M_det_old, r18["grid_movement_det"])):
            if got != want:
                drift.append([key, got, want])
        for c_new, c_old in zip(claims, r18["claims"]):
            for key in ("value", "nonseed_allowance", "A_seed"):
                if c_new[key] != c_old[key]:
                    drift.append([c_new["claim"] + "." + key,
                                  c_new[key], c_old[key]])
            if c_new["total_old"] != c_old["total_allowance_at_premise"]:
                drift.append([c_new["claim"] + ".total_old",
                              c_new["total_old"],
                              c_old["total_allowance_at_premise"]])
        blk["reprice_2718_drift"] = drift
        log("(%g, N=%d): reprice drift %d fields; claims %s"
            % (gamma, N, len(drift),
               [(c["claim"], c["GREEN_new"], "%.3g" % (c["margin_ratio_new"]
                                                       or 0))
                for c in claims]))
        results.append(blk)

    out = {
        "record": 2721,
        "title": "G1 swing 2c: analytic seed premise + ladder grid premise "
                 "(split-rule bridge over the logistic poles)",
        "scope": "stored record-1980 trial-owner models; sign claims only; "
                 "NO complete-owner claim, no map-103 reopening, no GO",
        "inputs": {
            "source_2032": "results/2032_gate_row_search.json",
            "source_2032_sha256":
                hashlib.sha256(SRC32.read_bytes()).hexdigest(),
            "source_2718": "results/2718_gate_sign_rig.json",
            "source_2718_sha256":
                hashlib.sha256(SRC18.read_bytes()).hexdigest(),
        },
        "method": {
            "seed_orders": (SEED_ORDER,) + SEED_ORDERS_STUDY,
            "grids": [DXI_PRIMARY, DXI_FINE, DXI_TAIL],
            "a_ladder": list(A_LADDER),
            "k_pole_max": K_POLE_MAX,
            "geo_tail": GEO_TAIL,
            "geo_tail_premise": "e(0.005) <= 1.0 x m(0.01,0.005) "
                                "(ratio-2 continuation; h^2 rung evidence "
                                "recorded per channel)",
            "E_seed_new": "D_float + 10 Lmax^9 B_tail (D_float = in-run "
                          "300-vs-1200 diff at the claim points incl. 0; "
                          "B_tail = d_split + round + strip_M + 2 strip_p "
                          "+ small_mass)",
        },
        "anchors": {
            "a3_seed0_bitwise": True,
            "a4_seed0_exact_gap": a4,
            "a1_bitwise_rows": {
                "%g_%d" % (r["gamma"], r["N"]):
                    r.get("anchor_bitwise_mismatches") for r in results},
            "a5_reprice_2718": {
                "%g_%d" % (r["gamma"], r["N"]):
                    len(r.get("reprice_2718_drift", [])) for r in results},
        },
        "rows": results,
        "producer_go": False, "family_reopened": False, "rh_claim": False,
        "smoke": SMOKE,
    }
    suffix = "_smoke" if SMOKE else ""
    (ROOT / ("results/2721_seed_premise_rig%s.json" % suffix)).write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    log("wrote results/2721_seed_premise_rig%s.json" % suffix)

    ok = (all(r.get("anchor_bitwise_mismatches") == 0 for r in results)
          and all(not r.get("reprice_2718_drift") for r in results)
          and all(c["GREEN_new"]
                  for r in results for c in r.get("claims", [])))
    print("RESULT 2721 %s" % ("GREEN: all sign claims re-certified at the "
          "analytic seed premise + ladder grid premise"
          if ok else "NOT GREEN: inspect claims/anchors/reprice"))


if __name__ == "__main__":
    main()
