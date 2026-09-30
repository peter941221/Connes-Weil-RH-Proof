"""Record 2306: grouped directed flat-edge tail bound for the corrected owner.

The 2304 mechanism (flat-edge N-fold integration by parts, no boundary
terms) charges the infinite tail by sup-norms of ONE real-variable
derivative:

    Tail = int_{|xi| > 40} kernel(xi) |ann(xi)|^2 |B(xi)|^2 |C(xi)|^2 dxi
    Tail <= 2 A1^2 (V_N^b V_N^c)^2 / (2 pi)^{4N}
            * int_40^inf (log xi + c_w) xi^{8-4N} dxi,

with V_N^ch = 2 Rmax sup_y |h_ch^{(N)}(y)| the sup of the FULL grouped
complex family sum

    h_ch(y) = sum_f c_f^{ch} phi_{R_f}(y) e^{(1/2 + i theta_f) y},
    R_f = a_f^2, phi_R(y) = exp(-K/(1-(y/R)^2)), K = 30,

and h_ch^{(N)} the exact N-th derivative.  2304 charged V_N through a
three-loss ladder: a decoupled partition majorant of the psi derivatives
(~1e17x loose at order 20), a familywise triangle over the 30 families,
and |E^{(m)}| <= (1/2 + |theta|)^m with the carrier phase e^{i theta y}
dropped.  This record replaces the ladder by a DIRECT evaluation of the
grouped complex derivative in the (u, s) variables of the psi-compression:

    h_f^{(N)}(y) = e^{lambda_f y} e^{-K/s_f} Q_f(y),
    u = y/R_f,  s_f = 1-u^2,
    Q_f(y) = sum_{j=0}^N C(N,j) lambda_f^{N-j} R_f^{-j} A_j(u) s_f^{-2j},

where psi^{(j)}(u) = psi(u) A_j(u) s^{-2j} with exact integer polynomials
A_j (A_0 = 1, A_{j+1} = s^2 A_j' + 2u(2j s - K) A_j).  The j-sum is
evaluated in u-space with positive powers s^{-2j} via a single log-scaled
exponential per term; an expanded y-polynomial form is REJECTED because
the binomial expansion of s^{2(N-j)} carries coefficient-magnitude sums
measured up to ~1e16x the value at |y/R| ~ 0.5, which would poison the
slack model (the u-path keeps the same ratio at <= ~1e5 measured).

The sup is enclosed on rational cells by a midpoint/mean-value scheme:

    ub(cell) = |sum_f c_f t_f(m)| + kappa * magchain
               + (Delta/2) sum_f |c_f| sup_{cell} |t_f'|

with t_f the family term, midpoint m, cell width Delta.  The cell sups
are honest triangle bounds built from |A_j(u)| <= magA_j(u_max) (the
coefficient triangle, an exact upper bound for the polynomial), the
unimodal sup  sup_{s in [s_lo,s_hi]} e^{-K/s} s^{-m} = e^{-K/s*} s*^{-m}
at s* = clip(K/m, s_lo, s_hi)  (m >= 1; m = 0 at s_hi), and derivative
bounds from the exact ODE identity

    A_j' = (A_{j+1} - 2u (2j s - K) A_j) / s^2

(A generated to order N+1; |2j s - K| <= 2j s_hi + K pointwise).

Audio model (declared, artifact grade): every computed binary64 quantity q
with tracked running magnitude M_q satisfies |q - q_true| <= kappa M_q;
kappa = 2^-30 by default, controlled by kappa-variation runs and by an
independent mpmath recomputation at the recorded argmax.  kappa carries
~7 decades of headroom over the binary64 unit roundoff (2^-53), so any
single-realization evaluation chain of up to ~1e6 rounding steps with
unit-size constants stays inside the declared slack.  The carrier
phases e^{i theta_f m} are kept exactly (grouping-before-modulus, the 2291
law); equal-theta families cancel inside the complex sum without any
interval width penalty.  The 2 Rmax factor in V_N is the integration-length
factor MISSING in 2304's v_ladder (erratum recorded in the doc).

Modes:
    MODE=selftest                      internal controls
    MODE=order ORDER=N [KAPPA_LOG2=k]  one order -> results/2306_order_N.json
    MODE=kcontrol N in {20,24,28}      kappa variation -> 2306_kc_N_k.json
    MODE=reduce                        tail table + verdict -> 2306_hgap_tail_sharp.json
    MODE=control                       mpmath argmax recomputation controls
"""
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
RES = ROOT / "results"
CAPTURE = RES / "2275_gap_owner_audit.json"
OUT_MAIN = RES / "2306_hgap_tail_sharp.json"
K = 30.0
XI0 = 40.0
BUDGET = 1.0e7
ORDERS = (8, 12, 16, 20, 24, 28, 32, 36, 40, 44)
GAMMA = 39.25244858548658
DELTA = 0.445
KAPPA = 2.0 ** -30
N0CELLS = 8192
ROUNDS = 6
TOPREF = 512
GRIDLB = 131072


def load_owner():
    cap = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    fam = [(float.fromhex(a), float.fromhex(t)) for a, t in cap["families_hex"]]
    base = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["base_hex"]])
    corr = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["corr_hex"]])
    return fam, base, corr, cap


# ----------------------------------------------------------- A_j machinery
def A_polys(jmax):
    """Integer coefficient lists (ascending), psi^{(j)} = psi A_j s^{-2j}.

    psi^{(j+1)} = (psi A_j s^{-2j})' gives the exact recursion
        A_{j+1} = s^2 A_j' + 2u (2j s - K) A_j,   s = 1-u^2,
    i.e. the psi'-leg contributes A_1 A_j = -2Ku A_j and the s-leg
    4ju s A_j; both are folded into the single factor 2u(2j s - K).
    """
    A = [[1]]
    for j in range(jmax):
        a = A[j]
        d = [(k + 1) * a[k + 1] for k in range(len(a) - 1)]
        m1 = [0] * (len(d) + 4)
        s2 = (1, 0, -2, 0, 1)
        for i, c in enumerate(d):
            for k, cc in enumerate(s2):
                m1[i + k] += c * cc
        p3 = (0, 2 * (2 * j - K), 0, -4 * j)
        m2 = [0] * (len(a) + 3)
        for i, c in enumerate(a):
            for k, cc in enumerate(p3):
                m2[i + k] += c * cc
        L = max(len(m1), len(m2))
        A.append([(m1[i] if i < len(m1) else 0) + (m2[i] if i < len(m2) else 0)
                  for i in range(L)])
    return A


def horner_r(coefs, x):
    out = np.zeros_like(x)
    for c in coefs[::-1]:
        out = out * x + c
    return out


def horner_mag(coefs, x):
    """Horner over |coeffs| at x >= 0: an honest sup bound on |p(u)|, |u|<=x."""
    out = np.zeros_like(x)
    for c in coefs[::-1]:
        out = out * x + abs(c)
    return out


def Sfun(m, s_lo, s_hi):
    """sup_{s in [s_lo, s_hi]} exp(-K/s) s^{-m} for m >= 0.

    The function is unimodal in s (monotone increasing for m = 0, interior
    maximum at s = K/m for m >= 1), so the sup sits at clip(K/m, lo, hi).
    """
    sl = np.maximum(s_lo, 1e-300)
    sh = np.maximum(s_hi, 1e-300)
    sc = sh if m == 0 else np.clip(K / m, sl, sh)
    with np.errstate(divide="ignore", over="ignore"):
        return np.exp(-K / sc - m * np.log(sc))


# ------------------------------------------------------------ cell bounds
def family_cell_arrays_u(R, th, N, A, ylo, yhi, kappa):
    """Upper-bound pieces of one family on cells [ylo, yhi], u-space path.

    Cells are pre-split at +-R_f.  The midpoint value is the exact bin64
    evaluation of Q_f(m) in (u, s) coordinates; the cell sup of |t_f| and
    |t_f'| are honest triangle bounds using the coefficient-triangle sup of
    |A_j| and the unimodal Sfun sup of e^{-K/s} s^{-m}.  A must be
    generated to order N+1 (the ODE identity needs A_{j+1}).
    """
    inside = (yhi <= R) & (ylo >= -R)
    m = 0.5 * (ylo + yhi)
    u_m = m / R
    umax = np.maximum(np.abs(ylo), np.abs(yhi)) / R
    sA = 1.0 - (ylo / R) ** 2
    sB = 1.0 - (yhi / R) ** 2
    s_lo = np.minimum(sA, sB)
    s_hi = np.where((ylo <= 0) & (0 <= yhi), 1.0, np.maximum(sA, sB))
    sm = 1.0 - u_m ** 2
    lam = 0.5 + 1j * th
    alam = math.hypot(0.5, th)
    lam_pow = [lam ** k for k in range(N + 1)]
    alam_pow = [alam ** k for k in range(N + 1)]
    with np.errstate(divide="ignore", over="ignore", invalid="ignore"):
        sm_safe = np.where(sm > 0, sm, 1.0)
        sm_mask = sm > 0
        base_exp = -K / sm_safe
        log_sm = np.log(sm_safe)
        t_sum = np.zeros_like(u_m, dtype=complex)
        mag_sum = np.zeros_like(u_m)
        qsup = np.zeros_like(u_m)
        qpsup = np.zeros_like(u_m)
        qpp = np.zeros_like(u_m)
        for j in range(N + 1):
            k = N - j
            cw = math.comb(N, j) * R ** (-j)
            aj = horner_r(A[j], u_m)
            magj = horner_mag(A[j], umax)
            wv = np.where(sm_mask, np.exp(base_exp - 2 * j * log_sm), 0.0)
            S2 = Sfun(2 * j, s_lo, s_hi)
            S2p = Sfun(2 * j + 2, s_lo, s_hi)
            t_sum += (cw * lam_pow[k]) * aj * wv
            mag_sum += (cw * alam_pow[k]) * magj * wv
            qsup += (cw * alam_pow[k]) * magj * S2
            qpp += (cw * alam_pow[k]) * magj * S2p
            if j:
                # |A_j'| s^{-2j} <= (|A_{j+1}| + 2|u|(2j s + K)|A_j|) s^{-2j-2}
                # (the s^{-2} soaks into the S(2j+2) clip; no raw 1/s_lo^2)
                magj1 = horner_mag(A[j + 1], umax)
                qpsup += (cw * alam_pow[k] / R) * (
                    (magj1 + 2 * umax * (2 * j * s_hi + K) * magj) * S2p
                    + 4 * j * umax * magj * Sfun(2 * j + 1, s_lo, s_hi))
        t_sum = np.where(inside, t_sum, 0.0)
        mag_sum = np.where(inside, mag_sum, 0.0)
        qsup = np.where(inside, qsup, 0.0)
        qpsup = np.where(inside, qpsup, 0.0)
        qpp = np.where(inside, qpp, 0.0)
    E_sup = np.where(inside, np.exp(np.minimum(yhi, R) / 2.0), 0.0)
    E_m = np.where(inside, np.exp(m / 2.0), 0.0)
    ph = np.exp(1j * th * m)
    t_m = E_m * ph * t_sum
    magt = E_m * mag_sum * (1.0 + 2 * kappa)
    term_sup = E_sup * qsup * (1.0 + 2 * kappa)
    dterm_sup = E_sup * (qpsup + (0.5 + abs(th)) * qsup
                         + (2.0 * K / R) * umax * qpp) * (1.0 + 2 * kappa)
    return {"t_m": t_m, "magt": magt, "term_sup": term_sup,
            "dterm_sup": dterm_sup, "inside": inside}


def ub_on_cells(fam, coefvec, N, A, ylo, yhi, kappa):
    """Grouped upper bounds per cell for one channel.  Returns (ub, lb, V)."""
    V = np.zeros_like(ylo, dtype=complex)
    mag = np.zeros_like(ylo)
    corr = np.zeros_like(ylo)
    for (R, th), c in zip(fam, coefvec):
        d = family_cell_arrays_u(R, th, N, A, ylo, yhi, kappa)
        V += c * d["t_m"]
        mag += abs(c) * d["magt"]
        corr += 0.5 * (yhi - ylo) * abs(c) * d["dterm_sup"]
    lb = np.abs(V)
    ub = lb + kappa * mag + corr
    return ub, lb, V


def refine_cells(ylo, yhi, ub, rounds=ROUNDS, top=TOPREF):
    for _ in range(rounds):
        idx = np.argsort(ub)[-top:]
        mid = 0.5 * (ylo[idx] + yhi[idx])
        keep = np.ones(len(ylo), dtype=bool)
        keep[idx] = False
        ylo = np.concatenate([ylo[keep], ylo[idx], mid])
        yhi = np.concatenate([yhi[keep], mid, yhi[idx]])
        ub = np.concatenate([ub[keep], ub[idx], ub[idx]])
    return ylo, yhi


def master_grid(fam, n0=N0CELLS):
    Rmax = max(a * a for a, _ in fam)
    cuts = sorted({-Rmax, Rmax}
                  | {a * a for a, _ in fam} | {-a * a for a, _ in fam})
    base = np.linspace(-Rmax, Rmax, n0 + 1)
    pts = np.unique(np.concatenate([base, np.array(cuts)]))
    return pts[:-1].copy(), pts[1:].copy(), Rmax


def dense_lb(fam, coefvec, N, A, Rmax, ngrid=GRIDLB):
    """Dense-grouped sampled lower bound (u-space Q_f, no corrections)."""
    y = np.linspace(-Rmax, Rmax, ngrid)
    V = np.zeros_like(y, dtype=complex)
    for (R, th), c in zip(fam, coefvec):
        u = y / R
        s = 1.0 - u * u
        lam = 0.5 + 1j * th
        with np.errstate(divide="ignore", over="ignore", invalid="ignore"):
            s_safe = np.where(s > 0, s, 1.0)
            mask = s > 0
            base_exp = -K / s_safe
            log_s = np.log(s_safe)
            tot = np.zeros_like(y, dtype=complex)
            for j in range(N + 1):
                wv = np.where(mask, np.exp(base_exp - 2 * j * log_s), 0.0)
                cl = math.comb(N, j) * R ** (-j) * lam ** (N - j)
                tot += cl * horner_r(A[j], u) * wv
        V += c * np.exp(y / 2.0) * np.exp(1j * th * y) * tot
    k = int(np.argmax(np.abs(V)))
    return float(np.abs(V[k])), float(y[k])


# ---------------------------------------------------- constants and tail
def annihilator_coeffs():
    rho = complex(0.5 + DELTA, GAMMA)
    nodes = [rho - 0.5, (1 - rho.conjugate()) - 0.5,
             rho.conjugate() - 0.5, (1 - rho) - 0.5]
    poly = np.array([1.0 + 0.0j])
    for node in nodes:
        poly = np.convolve(poly, np.array([-2j * math.pi, node]))
    coef = poly[::-1]
    return [float(v.real) for v in coef]


def kernel_cw():
    import fourpoint_diagonal_sign_1918 as rig
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    corr_bound = sum(abs(b) * 64.0 ** -kk for kk, b in enumerate(terms, start=1))
    harm = sum(1.0 / (jj + 0.25) for jj in range(8))
    slack = 0.5 * math.log1p(8.25 ** 2 / ((math.pi * XI0) ** 2))
    c_sigma = 2.0 * math.log(math.pi) + 0.5 / 8.0 + corr_bound + harm + slack
    primes = rig.prime_powers_up_to(math.exp(2.0 * 6.553600000000003))
    return c_sigma + 2.0 * sum(w / math.sqrt(n) for n, w in primes)


def tail_bound(N, Vb, Vc, a1, cw, mp):
    """mpmath 2 A1^2 (Vb Vc)^2 /(2 pi)^{4N} int_40^inf (log xi + cw) xi^{8-4N} dxi."""
    p = 4 * N - 8
    base = mp.mpf(XI0) ** (1 - p) / (p - 1)
    integ = base * (mp.log(XI0) + mp.mpf(1) / (p - 1)) + cw * base
    return (2 * a1 ** 2 * (Vb * Vc) ** 2 / (2 * mp.pi) ** (4 * N) * integ)


# -------------------------------------------------------------- order run
def run_order(N, kappa):
    import mpmath as mp
    mp.mp.dps = 40
    fam, base, corr, cap = load_owner()
    A = A_polys(N + 1)
    ylo, yhi, Rmax = master_grid(fam)
    ub_b, lb_b, _ = ub_on_cells(fam, base, N, A, ylo, yhi, kappa)
    ub_c, lb_c, _ = ub_on_cells(fam, corr, N, A, ylo, yhi, kappa)
    ub = np.maximum(ub_b, ub_c)
    if N >= 16:
        ylo, yhi = refine_cells(ylo, yhi, ub)
        ub_b, lb_b, _ = ub_on_cells(fam, base, N, A, ylo, yhi, kappa)
        ub_c, lb_c, _ = ub_on_cells(fam, corr, N, A, ylo, yhi, kappa)
    ib = int(np.argmax(ub_b))
    ic = int(np.argmax(ub_c))
    lbd_b, ylb_b = dense_lb(fam, base, N, A, Rmax)
    lbd_c, ylb_c = dense_lb(fam, corr, N, A, Rmax)
    ann = annihilator_coeffs()
    a1 = mp.mpf(repr(sum(abs(v) for v in ann)))
    cw = mp.mpf(repr(kernel_cw()))
    Vb = 2 * Rmax * mp.mpf(repr(float(ub_b[ib])))
    Vc = 2 * Rmax * mp.mpf(repr(float(ub_c[ic])))
    tail = tail_bound(N, Vb, Vc, a1, cw, mp)
    out = {
        "record": 2306, "order": N, "kappa_log2": math.log2(1 / kappa),
        "cells": int(len(ylo)), "Rmax": Rmax,
        "ub_base": float(ub_b[ib]), "ub_corr": float(ub_c[ic]),
        "argmax_y_base": float(0.5 * (ylo[ib] + yhi[ib])),
        "argmax_y_corr": float(0.5 * (ylo[ic] + yhi[ic])),
        "lb_dense_base": lbd_b, "lb_dense_corr": lbd_c,
        "argmax_y_dense_base": ylb_b, "argmax_y_dense_corr": ylb_c,
        "inflation_base": float(ub_b[ib]) / max(lbd_b, 1e-300),
        "inflation_corr": float(ub_c[ic]) / max(lbd_c, 1e-300),
        "V_base": mp.nstr(Vb, 10), "V_corr": mp.nstr(Vc, 10),
        "tail_bound": mp.nstr(tail, 10), "tail_float": float(tail),
        "margin": float(mp.mpf(BUDGET) / tail) if tail > 0 else float("inf"),
        "ann_l1": float(a1), "c_w": float(cw),
        "families": len(fam),
        "theta_groups": len({t for _, t in fam}),
    }
    OUTF = RES / f"2306_order_{N}.json"
    OUTF.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: out[k] for k in
                      ("order", "cells", "ub_base", "lb_dense_base",
                       "inflation_base", "inflation_corr", "tail_bound",
                       "margin", "argmax_y_base")}), flush=True)
    return out


def run_kcontrol(N, kappa):
    fam, base, corr, _ = load_owner()
    A = A_polys(N + 1)
    ylo, yhi, Rmax = master_grid(fam)
    ub_b, _, _ = ub_on_cells(fam, base, N, A, ylo, yhi, kappa)
    ub_c, _, _ = ub_on_cells(fam, corr, N, A, ylo, yhi, kappa)
    ub = np.maximum(ub_b, ub_c)
    for _ in range(ROUNDS):
        idx = np.argsort(ub)[-TOPREF:]
        mid = 0.5 * (ylo[idx] + yhi[idx])
        keep = np.ones(len(ylo), dtype=bool)
        keep[idx] = False
        ylo = np.concatenate([ylo[keep], ylo[idx], mid])
        yhi = np.concatenate([yhi[keep], mid, yhi[idx]])
        ub_b, _, _ = ub_on_cells(fam, base, N, A, ylo, yhi, kappa)
        ub_c, _, _ = ub_on_cells(fam, corr, N, A, ylo, yhi, kappa)
        ub = np.maximum(ub_b, ub_c)
    out = {"record": 2306, "order": N, "kappa_log2": math.log2(1 / kappa),
           "ub_base": float(np.max(ub_b)), "ub_corr": float(np.max(ub_c)),
           "cells": int(len(ylo))}
    (RES / f"2306_kc_{N}_k{int(math.log2(1 / kappa))}.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out), flush=True)


# ------------------------------------------------------------------ reduce
def reduce():
    import mpmath as mp
    mp.mp.dps = 40
    rows = []
    for N in ORDERS:
        f = RES / f"2306_order_{N}.json"
        if not f.exists():
            continue
        rows.append(json.loads(f.read_text(encoding="utf-8")))
    best = min(rows, key=lambda r: r["tail_float"])
    status = "TAIL-SHARP-COVERED" if best["tail_float"] <= BUDGET else "TAIL-SHARP-PRICED"
    out = {
        "record": 2306, "status": status, "certificate": False,
        "mechanism": "grouped directed sup of the exact Leibniz derivative; "
                     "flat-edge IBP remainder without boundary terms",
        "budget": BUDGET, "xi0": XI0, "kappa_log2_main": 30,
        "rows": rows, "best_order": best["order"],
        "best_tail_bound": best["tail_bound"],
        "best_tail_bound_float": best["tail_float"],
        "best_margin": best["margin"],
        "orders_dead": [r["order"] for r in rows
                        if r["tail_float"] > BUDGET],
        "erratum_2304": {
            "missing_length_factor": "2304's v_ladder omits the integration "
            "length 2 R_f per family; V_N here carries the single 2 Rmax "
            "factor instead of the familywise triangle",
            "price_arithmetic": "(2.9973776e17/1e7)^{1/4} = 416.1 (not 74); "
            "with the restored (2 Rmax)^4 = 2.95e4 length factor the price "
            "is 5450x per channel",
        },
        "controls": {
            "crosscheck_2304_N20": crosscheck_2304(),
            "kappa_variation": kappa_variation(),
        },
        "nonclaims": [
            "artifact grade: the binary64 evaluation carries a declared "
            "running-magnitude slack model (kappa = 2^-30), not a "
            "machine-verified interval certificate",
            "the kernel triangle bound, the prime-power sum and the "
            "annihilator l1 norm are not yet arithmetic-certified (2304's "
            "nonclaim, unchanged)",
            "the tail bound is an absolute-value bound; it does not supply "
            "the signed finite-window functional, the selected-owner "
            "readback or the producer margin",
            "no hgap certificate, no producer GO, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_hgap_tail_sharp_2306.py",
            "owner": "results/2275_gap_owner_audit.json",
            "predecessor": "results/2304_hgap_tail_moment_probe.json",
        },
    }
    OUT_MAIN.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "best_order": best["order"],
                      "best_tail_bound": best["tail_bound"],
                      "margin": best["margin"],
                      "covered_orders": [r["order"] for r in rows
                                         if r["tail_float"] <= BUDGET]},
                     indent=2), flush=True)


def crosscheck_2304():
    """Feed 2304's own V values through this record's tail formula."""
    import mpmath as mp
    mp.mp.dps = 40
    art = json.loads((RES / "2304_hgap_tail_moment_probe.json")
                     .read_text(encoding="utf-8"))
    rows = {r["order"]: r for r in art["rows"]}
    a1 = mp.mpf(repr(art["annihilator"]["l1"]))
    cw = mp.mpf(repr(art["kernel"]["c_w"]))
    out = []
    for N in (16, 20, 24, 28):
        r = rows[N]
        vb = mp.mpf(r["V_rigorous"]["base"])
        vc = mp.mpf(r["V_rigorous"]["corr"])
        mine = tail_bound(N, vb, vc, a1, cw, mp)
        theirs = mp.mpf(r["tail_bound_rigorous"])
        out.append({"order": N, "recomputed": mp.nstr(mine, 10),
                    "recorded": mp.nstr(theirs, 10),
                    "ratio": mp.nstr(mine / theirs, 8)})
    return {"control": "2304 V values through the 2306 tail formula",
            "rows": out}


def kappa_variation():
    out = []
    for f in sorted(RES.glob("2306_kc_*.json")):
        out.append(json.loads(f.read_text(encoding="utf-8")))
    return {"control": "kappa variation on orders 20/24/28", "rows": out}


# -------------------------------------------------------------- mp control
def control():
    """Independent mpmath recomputation at the recorded argmax of the best order.

    Uses the closed-form log-derivatives L_m(u) = -(K m!/2)[(1-u)^-(m+1)
    -/+ (1+u)^-(m+1)] and the complete Bell recursion psi^{(j)} = psi Y_j
    -- an arithmetic path that shares NO code with the A_j recursion.
    """
    import mpmath as mp
    mp.mp.dps = 50
    art = json.loads(OUT_MAIN.read_text(encoding="utf-8"))
    best = next(r for r in art["rows"] if r["order"] == art["best_order"])
    N = best["order"]
    fam, base, corr, _ = load_owner()
    out = {"control": "mpmath Bell-path recomputation", "order": N, "rows": []}
    for label, coefvec, ystar, ub in (
            ("base", base, best["argmax_y_base"], best["ub_base"]),
            ("corr", corr, best["argmax_y_corr"], best["ub_corr"])):
        y = mp.mpf(repr(ystar))
        tot = mp.mpc(0)
        for (R0, th), c in zip(fam, coefvec):
            R = mp.mpf(repr(R0))
            u = y / R
            s = 1 - u * u
            if s <= 0:
                continue
            psi = mp.e ** (-K / s)
            L = []
            for m in range(1, N + 1):
                t = (1 - u) ** (-(m + 1))
                t = t + (1 + u) ** (-(m + 1)) if m % 2 == 0 else \
                    t - (1 + u) ** (-(m + 1))
                L.append(-K * mp.factorial(m) / 2 * t)
            Y = [mp.mpf(1)]
            for j in range(1, N + 1):
                acc = mp.mpf(0)
                for i in range(j):
                    acc += mp.binomial(j - 1, i) * Y[j - 1 - i] * L[i]
                Y.append(acc)
            lam = mp.mpf("0.5") + 1j * mp.mpf(repr(th))
            hN = mp.mpc(0)
            for j in range(N + 1):
                phij = psi * Y[j] * R ** (-j)
                hN += mp.binomial(N, j) * phij * lam ** (N - j)
            tot += mp.mpc(c.real, c.imag) * mp.e ** (lam * y) * hN
        val = abs(tot)
        out["rows"].append({"channel": label, "y": ystar,
                            "mp_abs_T": mp.nstr(val, 12),
                            "cell_ub": ub, "ub_over_mp": float(mp.mpf(ub) / val)
                            if val > 0 else None})
    (RES / "2306_mp_control.json").write_text(json.dumps(out, indent=2) + "\n",
                                              encoding="utf-8")
    print(json.dumps(out, indent=2), flush=True)


# -------------------------------------------------------------- selftest
def selftest():
    import mpmath as mp
    mp.mp.dps = 40
    fam, base, corr, _ = load_owner()
    ok = True
    res = {}
    # 1. A_j against the closed-form Bell evaluation of psi^{(j)}
    A = A_polys(8)
    worst = 0.0
    for u in (0.1, 0.37, 0.62, -0.44):
        um = mp.mpf(repr(u))
        s = 1 - um * um
        psi = mp.e ** (-K / s)
        # closed form log derivatives L_m
        L = []
        for m in range(1, 9):
            t = (1 - um) ** (-(m + 1))
            t = t + (1 + um) ** (-(m + 1)) if m % 2 == 0 else \
                t - (1 + um) ** (-(m + 1))
            L.append(-K * mp.factorial(m) / 2 * t)
        Y = [mp.mpf(1)]
        for j in range(1, 9):
            acc = mp.mpf(0)
            for i in range(j):
                acc += mp.binomial(j - 1, i) * Y[j - 1 - i] * L[i]
            Y.append(acc)
            aj = mp.mpf(0)
            for k, ck in enumerate(A[j]):
                aj += mp.mpf(ck) * um ** k
            lhs = psi * Y[j]
            rhs = psi * aj * s ** (-2 * j)
            worst = max(worst, float(abs(lhs - rhs) / abs(lhs)))
    ok &= worst < 1e-25
    res["A_j_bell_worst_rel"] = worst
    # 2. u-space value path (bin64, production) vs the mpmath Leibniz sum
    #    with POSITIVE powers s^{2(N-j)} divided by s^{2N} at the end --
    #    an arithmetically independent arrangement of the same object.
    N = 6
    A6 = A_polys(N + 1)
    yv = 1.234
    w2 = 0.0
    for (R0, th) in fam[:5]:
        R = mp.mpf(repr(R0))
        u = mp.mpf(repr(yv)) / R
        s = 1 - u * u
        lam = mp.mpf("0.5") + 1j * mp.mpf(repr(th))
        inner = mp.mpc(0)
        for j in range(N + 1):
            aj = sum(mp.mpf(ck) * u ** k for k, ck in enumerate(A6[j]))
            inner += mp.binomial(N, j) * (R * lam) ** (N - j) * aj \
                * s ** (2 * (N - j))
        ref = mp.e ** (lam * yv) * mp.e ** (-K / s) * inner / (s ** (2 * N) * R ** N)
        d = family_cell_arrays_u(R0, th, N, A6,
                                 np.array([yv - 1e-6]), np.array([yv + 1e-6]),
                                 KAPPA)
        w2 = max(w2, float(abs(d["t_m"][0] - ref) / abs(ref)))
    ok &= w2 < 1e-9
    res["ujsum_vs_mp_leibniz_worst_rel"] = w2
    # 2b. ODE identity A_j' = (A_{j+1} - 2u(2js-K)A_j)/s^2 vs central diff
    w2b = 0.0
    for j in (1, 3, 5):
        u0 = mp.mpf("0.37")
        hh = mp.mpf("1e-6")
        s0 = 1 - u0 * u0
        a0 = sum(mp.mpf(ck) * u0 ** k for k, ck in enumerate(A6[j]))
        a1_ = sum(mp.mpf(ck) * u0 ** k for k, ck in enumerate(A6[j + 1]))
        am = sum(mp.mpf(ck) * (u0 - hh) ** k for k, ck in enumerate(A6[j]))
        ap = sum(mp.mpf(ck) * (u0 + hh) ** k for k, ck in enumerate(A6[j]))
        fd = (ap - am) / (2 * hh)
        ident = (a1_ - 2 * u0 * (2 * j * s0 - K) * a0) / s0 ** 2
        w2b = max(w2b, float(abs(fd - ident) / abs(ident)))
    ok &= w2b < 1e-5
    res["A_ode_identity_fd_worst_rel"] = w2b
    # 3. tail formula reproduces 2304's recorded rigorous bound
    art = json.loads((RES / "2304_hgap_tail_moment_probe.json")
                     .read_text(encoding="utf-8"))
    r20 = next(r for r in art["rows"] if r["order"] == 20)
    a1 = mp.mpf(repr(art["annihilator"]["l1"]))
    cw = mp.mpf(repr(art["kernel"]["c_w"]))
    mine = tail_bound(20, mp.mpf(r20["V_rigorous"]["base"]),
                      mp.mpf(r20["V_rigorous"]["corr"]), a1, cw, mp)
    rat = float(mine / mp.mpf(r20["tail_bound_rigorous"]))
    ok &= abs(rat - 1) < 1e-6
    res["tail_formula_2304_ratio"] = rat
    # 4. ub >= lb on a small order, both channels
    Ns = 12
    As = A_polys(Ns + 1)
    ylo, yhi, Rmax = master_grid(fam, 512)
    for vec in (base, corr):
        ub, lb, _ = ub_on_cells(fam, vec, Ns, As, ylo, yhi, KAPPA)
        ok &= bool(np.all(ub >= lb * (1 - 1e-12)))
        res.setdefault("ub_ge_lb", True)
    # 5. declared group count
    res["theta_groups"] = len({t for _, t in fam})
    ok &= res["theta_groups"] == 25
    print(json.dumps({"selftest": "PASS" if ok else "FAIL", **res},
                     indent=2), flush=True)
    return ok


def main():
    mode = os.environ.get("MODE", "selftest")
    kappa = 2.0 ** -float(os.environ.get("KAPPA_LOG2", "30"))
    if mode == "selftest":
        if not selftest():
            raise SystemExit("selftest failed")
    elif mode == "order":
        run_order(int(os.environ["ORDER"]), kappa)
    elif mode == "kcontrol":
        run_kcontrol(int(os.environ["ORDER"]), kappa)
    elif mode == "reduce":
        reduce()
    elif mode == "control":
        control()
    else:
        raise SystemExit(f"unknown MODE {mode}")


if __name__ == "__main__":
    main()