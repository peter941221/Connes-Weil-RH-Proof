#!/usr/bin/env python3
"""2720 - P3 certified strip-decay constants (q*, C4*, C2*) for the explicit
route base/correction objects at the two n=3 candidate rows.

Consumes: the record-2708 contract P3 duty (the three forall-strip
hypotheses of selectedOwner_fullOrbitSpan_fourthOrderSpectralTail_of_q),
named in the map-103 reopen probe after records 2716/2717/2718/2719.

Owner objects (explicit route choice, recorded here):
  base       = cardinal over the 8 healthy TARGETS with y == 1,
  correction = cardinal over the OWNER with y = target_value (3 active
               nodes: rho -> +1, 1-conj(rho) -> -1, rho+0.5 -> -1),
  seed       = f_tilde^{*10}, f_tilde = 2 f(2u), f = smooth_seed_raw.
The seed transform is EXACT: L_pow(s) = L1(s/2)^10 with
  L1(u) = int_{-2}^{2} e^{u x} f(x) dx,   seed0 = L_pow(0) = 3^10 = 59049
(the Lean-certified laplaceAt smoothSeed 0 = 3, powered and scaled).
This is the object the record-2032/2033 pipeline evaluates through its
order-300 GL discretization (SEED_SCALE = 0.5, SEED_POWER = 10); the
certified instrument bounds the TRUE transforms, so the tail side no
longer leans on an E_seed-style observational premise.

Method (fully certified, no observational premises):
  S1  seed derivative constants D_k = 2 int_0^1 |T^{(k)}| (k = 1..12),
      T = 1/(1+exp(-phi)), phi = 1/u - 1/(1-u) > 0 on (0, 1/2]
      (loop-stable branch), certified by ONE mp.iv truncated-derivative
      jet (order 13) per partition cell of [1/4096, 1/2], x2 symmetry
      (|T^{(k)}(u)| = |T^{(k)}(1-u)|, from T(u) = 1 - T(1-u)), interval
      extension over each cell (no monotonicity assumption), sliver
      (0, 1/4096] charged by the neighbor-cell iv sup x 8 x width
      (analytic rate e^{-1/u} u^{-2k}(1+O(u)); in-run point scan as
      evidence).  Closed-form controls: D_1 = 2, D_2 = 8 enclosed.
  S2  per-term envelope, one variable t (sigma eliminated by endpoint
      maxima: each |z_w - s| factor is maximized over sigma in [0,1] at
      an endpoint; every seed piece carries its sigma-sup constant):
        term_z(t) = |c_z| * MQ_z(t) * Psi_z(t)^10,
        MQ_z(t) = prod_{w != z} sqrt(ds_w^2 + max_s |t - Im w|^2),
        ds_w = max(|Re w|, |1 - Re w|)   (sigma endpoint max),
        Psi_z(t) = min(3 e^{r_z}, min_k e^{r_z} D_k 2^k/|t-Im z|^k),
        r_z = max(Re z, 1 - Re z, 0)     (sigma-sup of 2|Re((s-z)/2)|),
        c_z = y_z / (Q_z(z) * 59049), outward 1e-12 pads.
      All envelope arithmetic in padded mpf uppers (min-of-uppers is an
      upper; every factor explicitly rounded outward).  Cell sup =
      max(endpoint uppers) + (h/2) * sup|E'| (Lipschitz: |dM_w/dt| <= 1
      law, min-piece derivative bounded by max over pieces).  Tail:
      geometric ladder to 1e4 + MVT slack per ladder cell.
  S3  strip constants: q*(T) = sup_{|t| >= T} C_base(t) at T in
      {16, 32, 64}; C4* = sup_t (|t|/2pi)^4 C_base(t);
      C2* = sup_t (|t|/2pi)^2 C_corr(t).  |t| symmetry is NOT assumed
      (nodes sit at both heights); the scan covers both signs.
  S4  coverage: the envelope must dominate the record-2033-style
      L300-cardinal sample (op.cardinal_transform with
      make_powered_seed) + 1e-9 pad at every (sigma, t) grid point,
      both channels, both rows.  This is the convention/sign bugcatch.
  S5  joint repricing: tau(n, lam) = H^4 (2 pi)^12 (C4 C2)^2 q^(2n)
      (1 + H^4/|lam|)^2 with the CERTIFIED constants swapped in
      (formulas verbatim from the committed record-2033 script);
      F_total(n) = (q_eff^n C4* C2*)/(q^n C4 C2); lim*(n) = a0* q^(2n);
      lam_min*(n) = H^4 / (1/sqrt(lim*) - 1); F_max(n) budget table;
      joint-compatibility verdict against the record-2718 branch data
      (row A rays lam >= 1381.53; row B all, lam > 15.86).

Model constants: the stored binary64 node sets (record-1980 builder) are
the owner definition; the node-radius/owner transfer brick stays open.

Writes results/2720_p3_certified_strip_constants.json.  No Lean theorem,
no producer GO, no map-103 reopening, no RH claim.
"""

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

import fourpoint_actual_owner_1980 as op  # noqa: E402
import fourpoint_powered_seed_1981 as p81  # noqa: E402

RECORD = 2720
DATE = "2026-10-16"
T_START = time.time()

mp.mp.dps = 40
mp.iv.dps = 30

Q_SAMPLED = 2.0 ** -14
TWO_PI_12 = (2.0 * math.pi) ** 12
SEED0 = 3.0 ** 10           # 59049 exact
K_MAX = 12                  # seed ladder depth
SLIVER_HI = mp.mpf(1) / 4096
SLIVER_SAFETY = 8
TAIL_T = 600.0
TAIL_STEP = 1.05
PAD_COVER = 1e-9
PAD_UP = 1 + mp.mpf(10) ** -18      # envelope arithmetic pad (relative)
COMPACT_PAD = 30.0                  # compact zone = max active |Im| + this
GRID_H = 0.1
GRID_H_FINE = 0.005
FINE_WINDOW = 2.0

CANDIDATES = [
    {"gamma": 14.134725141734693, "re": 0.55, "N": 4,
     "branch": "rays", "branch_lambda_min": 1381.53,
     "sampled_C4": 152.96406643093619, "sampled_C2": 683.8644420520491},
    {"gamma": 21.022039638771556, "re": 0.55, "N": 5,
     "branch": "all", "branch_lambda_min": 15.86,
     "sampled_C4": 624.4643392815566, "sampled_C2": 1913.288591837906},
]

OUTPUT = ROOT / "results" / "2720_p3_certified_strip_constants.json"
LOG_LINES = []


def log(msg):
    line = "[%7.1fs] %s" % (time.time() - T_START, msg)
    LOG_LINES.append(line)
    print(line, flush=True)


def up(x):
    """Outward upper endpoint of an iv interval, as mpf."""
    return mp.mpf(x.b)


def absup(comp):
    """sup |comp| for an iv component, as mpf (degenerate endpoints)."""
    return max(abs(mp.mpf(comp.a)), abs(mp.mpf(comp.b)))


# --------------------------------------------------------------------------
# S1: certified seed derivative constants D_k
# --------------------------------------------------------------------------

def jet_recip(X):
    """Derivative-sequence jet of 1/X (binomial product rule).

    X*Y = 1 componentwise:  sum_j C(k, j) X_j Y_{k-j} = delta_{k,0}.
    """
    n = len(X)
    Y = [None] * n
    Y[0] = 1 / X[0]
    for k in range(1, n):
        acc = mp.iv.mpf(0)
        for j in range(1, k + 1):
            acc += math.comb(k, j) * X[j] * Y[k - j]
        Y[k] = -acc / X[0]
    return Y


def jet_exp(X):
    """Derivative-sequence jet of exp(X): Y' = X' (x) Y with binomials,

    Y_{k+1} = sum_{j=0}^{k} C(k, j) X_{j+1} Y_{k-j}.
    """
    n = len(X)
    Y = [None] * n
    Y[0] = mp.iv.exp(X[0])
    for k in range(n - 1):
        acc = mp.iv.mpf(0)
        for j in range(k + 1):
            acc += math.comb(k, j) * X[j + 1] * Y[k - j]
        Y[k + 1] = acc
    return Y


def jet_sub(A, B):
    return [a - b for a, b in zip(A, B)]


def jet_mul(A, B):
    """Derivative-sequence product: (AB)_k = sum_j C(k, j) A_j B_{k-j}."""
    n = len(A)
    return [sum(math.comb(k, j) * A[j] * B[k - j] for j in range(k + 1))
            for k in range(n)]


def seed_jet(u_iv, order):
    n = order + 1
    U = [mp.iv.mpf(0)] * n
    U[0] = u_iv
    if n > 1:
        U[1] = mp.iv.mpf(1)
    inv_u = jet_recip(U)
    om = [mp.iv.mpf(0)] * n
    om[0] = 1 - u_iv
    if n > 1:
        om[1] = mp.iv.mpf(-1)
    inv_om = jet_recip(om)
    phi = jet_sub(inv_u, inv_om)
    E = jet_exp([-x for x in phi])
    one = [mp.iv.mpf(0)] * n
    one[0] = mp.iv.mpf(1)
    denom = [e + o for e, o in zip(E, one)]   # 1 + E
    inv_den = jet_recip(denom)
    return jet_mul(E, inv_den)                # T = E / (1 + E)


def certified_D_table():
    """D_k = 4 int_0^{1/2} |T^{(k)}| du for k = 1..K_MAX, certified."""
    n_cells = 4096
    lo_start = mp.mpf(1) / 4096
    hi_half = mp.mpf(1) / 2
    h = (hi_half - lo_start) / n_cells
    acc = {k: mp.iv.mpf(0) for k in range(1, K_MAX + 1)}
    for i in range(n_cells):
        a = lo_start + i * h
        b = a + h
        cell = mp.iv.mpf([a, b])
        J = seed_jet(cell, K_MAX)
        width = mp.iv.mpf([h, h])
        for k in range(1, K_MAX + 1):
            mag = absup(J[k])
            acc[k] += width * mp.iv.mpf([mp.mpf(0), mag])
    # sliver (0, 1/4096]: neighbor-cell iv sup x safety x width
    Jsl = seed_jet(mp.iv.mpf([SLIVER_HI / 2, SLIVER_HI]), K_MAX)
    D = {}
    sliver_frac = {}
    for k in range(1, K_MAX + 1):
        sl_sup = absup(Jsl[k])
        sliver = SLIVER_SAFETY * SLIVER_HI * sl_sup
        Dk = up(4 * (acc[k] + sliver))
        D[k] = Dk
        sliver_frac[k] = sliver
    checks = {1: bool(mp.mpf(2) <= D[1]),
              2: bool(mp.mpf(8) <= D[2])}
    return D, checks


def sliver_scan(k_samples, n_pts=1024):
    """Evidence: sliver point values never exceed neighbor sup x 8."""
    nb = {}
    Jsl = seed_jet(mp.iv.mpf([SLIVER_HI / 2, SLIVER_HI]), K_MAX)
    for k in k_samples:
        nb[k] = absup(Jsl[k])
    worst = 0.0
    for i in range(n_pts):
        u = SLIVER_HI / 2 * (i + 1) / n_pts
        for k in k_samples:
            J = seed_jet(mp.iv.mpf([u, u]), k)
            v = absup(J[k])
            if nb[k] > 0:
                worst = max(worst, float(v / (SLIVER_SAFETY * nb[k])))
    return worst


# --------------------------------------------------------------------------
# S2/S3: envelope machinery (padded mpf uppers throughout)
# --------------------------------------------------------------------------

def make_consts(nodes, ys):
    """Per-nonzero-node envelope constants with outward pads.

    Q and c_abs are built over the FULL node list (every owner node
    appears in the product and the denominator), matching the sampled
    cardinal exactly; nodes with y == 0 contribute no term.
    """
    out = []
    for z, y in zip(nodes, ys):
        if abs(y) == 0.0:
            continue
        Q = mp.mpc(1)
        for w in nodes:
            if w != z:
                Q = Q * mp.mpc(w.real - z.real, w.imag - z.imag)
        c_abs = float(abs(y) / (abs(Q) * mp.mpf(SEED0))) * (1 + 1e-12)
        r = max(float(z.real), 1.0 - float(z.real), 0.0)
        others = [(mp.mpf(max(abs(w.real), abs(1.0 - w.real))),
                   mp.mpf(w.imag)) for w in nodes if w != z]
        out.append({"z": z, "c_abs": mp.mpf(c_abs), "others": others,
                    "Ez": mp.exp(mp.mpf(r)) * (1 + mp.mpf(10) ** -25),
                    "im": mp.mpf(z.imag)})
    return out


def envelope_cell(consts, t_lo, t_hi, k_table, want_deriv):
    """Upper envelope C(t) over [t_lo, t_hi]; returns (C_up, dC_up) mpf."""
    total = mp.mpf(0)
    dtotal = mp.mpf(0)
    for cz in consts:
        z = cz["z"]
        # MQ_z over the t-cell: product over ALL other owner nodes
        MQ = mp.mpf(1)
        M_max = mp.mpf(0)
        m = 0
        for ds_w, im_w in cz["others"]:
            dtau_hi = max(abs(t_lo - im_w), abs(t_hi - im_w))
            Mw = mp.sqrt(ds_w * ds_w + dtau_hi * dtau_hi)
            MQ *= Mw
            M_max = max(M_max, Mw)
            m += 1
        MQ *= 1 + mp.mpf(10) ** -25
        tau_lo = min(abs(t_lo - cz["im"]), abs(t_hi - cz["im"]))
        pieces = [3 * cz["Ez"]]
        dpieces = [mp.mpf(0)]
        if tau_lo > 0:
            for k in range(1, K_MAX + 1):
                # |L1| <= e^{2 sup|Re u|} D_k / |Im u|^k, |Im u| = tau/2:
                # bound = Ez * D_k * 2^k / tau^k
                val = cz["Ez"] * k_table[k] * (mp.mpf(2) ** k) \
                    / tau_lo ** k
                val *= 1 + mp.mpf(10) ** -25
                pieces.append(val)
                dpieces.append(k * val / tau_lo)
        Psi = min(pieces)
        Psi10 = Psi ** 10
        total += cz["c_abs"] * MQ * Psi10 * PAD_UP
        if want_deriv:
            dMQ = m * M_max ** (m - 1) if m > 0 else mp.mpf(0)
            dPsi = max(dpieces)
            dtotal += cz["c_abs"] * (dMQ * Psi10
                                     + MQ * 10 * Psi ** 9 * dPsi) * PAD_UP
    return total, dtotal


def scan_cells(active_im):
    """Interval cells covering [0, T_end]: coarse 0.05 grid OVERLAID by
    0.005 fine cells near active heights (overlapping covers are sound;
    the sup takes the max over all cells)."""
    cells = []
    T_end = max(active_im) + COMPACT_PAD
    t = 0.0
    while t < T_end:
        t2 = min(t + GRID_H, T_end)
        if t2 > t + 1e-15:
            cells.append((t, t2))
        t = t2
    for zi in active_im:
        if zi <= 0:
            continue
        t = max(0.0, zi - FINE_WINDOW)
        while t < zi + FINE_WINDOW:
            t2 = min(t + GRID_H_FINE, zi + FINE_WINDOW)
            if t2 > t + 1e-15:
                cells.append((t, t2))
            t = t2
    cells.sort()
    return cells, T_end


def cell_val(consts, lo, hi, k_table, weight_p, sgn):
    """Sound cell upper for C and C*w over sgn*[lo, hi] (hi >= lo >= 0)."""
    if sgn > 0:
        val, _ = envelope_cell(consts, mp.mpf(lo), mp.mpf(hi), k_table,
                               False)
    else:
        val, _ = envelope_cell(consts, mp.mpf(-hi), mp.mpf(-lo), k_table,
                               False)
    w_lo = (mp.mpf(lo) / (2 * math.pi)) ** weight_p if lo > 0 else mp.mpf(0)
    w_hi = (mp.mpf(hi) / (2 * math.pi)) ** weight_p
    return val, val * max(w_lo, w_hi)


def scan_channel(consts, weight_p, k_table):
    """C4*/C2* style weighted sup over all t (both signs); interval cells."""
    active_im = [float(c["im"]) for c in consts]
    cells, T_end = scan_cells(active_im)
    sup = mp.mpf(0)
    sup_w = mp.mpf(0)
    for lo, hi in cells:
        for sgn in (1, -1):
            v, vw = cell_val(consts, lo, hi, k_table, weight_p, sgn)
            sup = max(sup, v)
            sup_w = max(sup_w, vw)
    # tail ladder to TAIL_T (refined step: IBP pieces carry (hi/lo)^k)
    t = T_end
    while t < TAIL_T:
        t2 = min(t * TAIL_STEP, TAIL_T)
        v, vw = cell_val(consts, t, t2, k_table, weight_p, 1)
        v2, vw2 = cell_val(consts, t, t2, k_table, weight_p, -1)
        sup = max(sup, v, v2)
        sup_w = max(sup_w, vw, vw2)
        sup = max(sup, v)
        sup_w = max(sup_w, vw)
        t = t2
    return float(up(mp.iv.mpf([sup, sup]))), \
        float(up(mp.iv.mpf([sup_w, sup_w])))


def q_star_at(consts, T, k_table):
    """sup_{|t| >= T} C_base(t): interval cells + refined tail ladder."""
    active_im = [float(c["im"]) for c in consts]
    cells = []
    t = float(T)
    while t < TAIL_T:
        t2 = min(t * TAIL_STEP, TAIL_T)
        if t2 > t + 1e-15:
            cells.append((t, t2))
        t = t2
    # fine cells hugging any active height in [T, ...]
    for zi in active_im:
        if zi >= float(T) - FINE_WINDOW:
            t = max(float(T), zi - FINE_WINDOW)
            while t < zi + FINE_WINDOW:
                t2 = min(t + GRID_H_FINE, zi + FINE_WINDOW)
                if t2 > t + 1e-15:
                    cells.append((t, t2))
                t = t2
    sup = mp.mpf(0)
    for lo, hi in sorted(cells):
        for sgn in (1, -1):
            v, _ = cell_val(consts, lo, hi, k_table, 4, sgn)
            sup = max(sup, v)
    return float(up(mp.iv.mpf([sup, sup])))


# --------------------------------------------------------------------------
# S4: coverage against the L300 pipeline cardinal
# --------------------------------------------------------------------------

def coverage_check(row, seed_transform, cb, cc, k_table):
    fails = 0
    worst = 0.0
    worst_pts = []
    for sigma in (0.0, 0.5, 1.0):
        for h in np.linspace(0.0, 200.0, 81):
            for sign in (1, -1):
                s = complex(sigma, sign * float(h))
                lb = op.cardinal_transform(row.targets, row.base_values,
                                           SEED0, s, seed_transform)
                lc = op.cardinal_transform(row.owner, row.values,
                                           SEED0, s, seed_transform)
                tt = mp.mpf(sign * float(h))
                eb, _ = envelope_cell(cb, tt, tt, k_table, False)
                ec, _ = envelope_cell(cc, tt, tt, k_table, False)
                for chan, sampled, env in (("base", abs(lb), eb),
                                           ("corr", abs(lc), ec)):
                    need = mp.mpf(float(sampled)) * (1 + PAD_COVER)
                    if env < need:
                        fails += 1
                        worst_pts.append({
                            "sigma": sigma, "h": float(h), "sign": sign,
                            "channel": chan, "sampled": float(sampled),
                            "envelope": float(env),
                            "ratio": float(need / max(env, mp.mpf(10)
                                                      ** -300))})
                    worst = max(worst,
                                float(need / max(env, mp.mpf(10) ** -300)))
    worst_pts.sort(key=lambda p: -p["ratio"])
    return {"fails": fails, "worst_sampled_over_envelope": worst,
            "worst_points": worst_pts[:5]}


# --------------------------------------------------------------------------
# S5: joint repricing (2033 formulas verbatim)
# --------------------------------------------------------------------------

def lam_min_for(H, c4, c2, n, q):
    a0 = H ** 4 * TWO_PI_12 * (c4 * c2) ** 2
    lim = a0 * q ** (2 * n)
    if lim >= 1.0:
        return None, lim
    return H ** 4 / (1.0 / math.sqrt(lim) - 1.0), lim


def main():
    log("2720 P3 certified strip constants: start")
    D, checks = certified_D_table()
    log("S1 D_table: %s" % json.dumps(
        {k: float(D[k]) for k in sorted(D)}))
    log("S1 closed-form controls (D_1=2, D_2=8 enclosed): %s"
        % json.dumps(checks))
    worst_sliver = sliver_scan([2, 6, 12])
    log("S1 sliver scan worst fraction of the charged bound: %.3e"
        % worst_sliver)

    seed_transform = p81.make_powered_seed()
    rows_out = []
    for cand in CANDIDATES:
        row = Row_(cand)
        cb = make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
        # correction consts over the FULL owner list (products and c_z
        # over all nodes; only the +-1 nodes contribute terms), matching
        # the sampled cardinal object exactly
        cc = make_consts(row.owner, row.values)
        log("row (%.4f,N=%d): owner=%d corr_active=%d H=%.4f"
            % (cand["gamma"], cand["N"], len(row.owner), len(cc), row.H))
        sup_b, C4c = scan_channel(cb, 4, D)
        sup_c, C2c = scan_channel(cc, 2, D)
        log("  base: sup=%.6e C4*=%.6e (sampled %.6e, F=%.3e)"
            % (sup_b, C4c, cand["sampled_C4"], C4c / cand["sampled_C4"]))
        log("  corr: sup=%.6e C2*=%.6e (sampled %.6e, F=%.3e)"
            % (sup_c, C2c, cand["sampled_C2"], C2c / cand["sampled_C2"]))
        qstars = {str(int(T)): q_star_at(cb, T, D)
                  for T in (16, 32, 64)}
        log("  q*(T): %s" % json.dumps(qstars))
        cov = coverage_check(row, seed_transform, cb, cc, D)
        log("  coverage: fails=%d worst=%.3e"
            % (cov["fails"], cov["worst_sampled_over_envelope"]))
        if cov["fails"]:
            log("  coverage worst points: %s"
                % json.dumps(cov["worst_points"]))
        # Two lanes:
        #  PAIR   — the certified (T, q*(T)) pair with the P4 threshold
        #           cap T <= 2^(N+1); the contraction premise is the
        #           certified q*, so its 2n power prices against C4*C2.
        #  KEEP-Q — the sampled contraction 2^-14 kept, certified C4*/C2*
        #           priced against the 2033 F_max budget (the previous
        #           reading).
        T_pair = 2 ** (cand["N"] + 1)
        q_pair = float(qstars[str(T_pair)])
        H = row.H
        n_table = []
        for n in range(3, 7):
            a0s = H ** 4 * TWO_PI_12 * (cand["sampled_C4"]
                                        * cand["sampled_C2"]) ** 2
            lim_s = a0s * Q_SAMPLED ** (2 * n)
            fmax = (1.0 / math.sqrt(lim_s) if 0 < lim_s < 1 else None)
            F_total = ((Q_SAMPLED ** n * C4c * C2c)
                       / (Q_SAMPLED ** n * cand["sampled_C4"]
                          * cand["sampled_C2"]))
            lmin_c, lim_c = lam_min_for(H, C4c, C2c, n, Q_SAMPLED)
            lmin_s, _ = lam_min_for(H, cand["sampled_C4"],
                                    cand["sampled_C2"], n, Q_SAMPLED)
            lmin_p, lim_p = lam_min_for(H, C4c, C2c, n, q_pair)
            n_table.append({
                "n": n, "F_total": F_total, "F_max": fmax,
                "lim_keepq": lim_c, "lim_sampled": lim_s,
                "lam_min_keepq": lmin_c, "lam_min_sampled": lmin_s,
                "joint_keepq": bool(lim_c < 1.0),
                "lim_pair": lim_p, "lam_min_pair": lmin_p,
                "joint_pair": bool(lim_p < 1.0),
            })
        rows_out.append({
            "gamma": cand["gamma"], "N": cand["N"],
            "rho": [row.rho.real, row.rho.imag], "H": H,
            "radius": row.radius,
            "owner_cardinality": len(row.owner),
            "corr_active": len(cc),
            "certified": {"q_star_T16": qstars["16"],
                          "q_star_T32": qstars["32"],
                          "q_star_T64": qstars["64"],
                          "C4_star": C4c, "C2_star_corr": C2c,
                          "base_sup_unweighted": sup_b,
                          "corr_sup_unweighted": sup_c},
            "sampled_2033": {"base_C4": cand["sampled_C4"],
                             "correction_C2": cand["sampled_C2"],
                             "q": Q_SAMPLED},
            "inflation": {"F_C4": C4c / cand["sampled_C4"],
                          "F_C2": C2c / cand["sampled_C2"],
                          "q_pair_over_q": q_pair / Q_SAMPLED},
            "coverage": cov,
            "repricing": {"T_pair": T_pair, "q_pair": q_pair,
                          "n_table": n_table},
            "branch_2718": {"branch": cand["branch"],
                            "lambda_min": cand["branch_lambda_min"]},
        })
        log("  n=3 KEEP-Q: F_total=%.3e F_max=%s joint=%s | PAIR: "
            "T=%d q*=%.3e lim=%.3e joint=%s" % (
                n_table[0]["F_total"], n_table[0]["F_max"],
                n_table[0]["joint_keepq"], T_pair, q_pair,
                n_table[0]["lim_pair"], n_table[0]["joint_pair"]))
    all_cov_ok = all(r["coverage"]["fails"] == 0 for r in rows_out)
    status = ("P3-CERTIFIED-CONSTANTS-REPRICED"
              if all_cov_ok else "P3-COVERAGE-FAIL")
    result = {
        "record": RECORD, "date": DATE, "status": status,
        "seed_identity": {
            "seed": "f_tilde^{*10}, f_tilde = 2 f(2u), f = smooth_seed_raw",
            "transform": "L_pow(s) = L1(s/2)^10",
            "seed0": SEED0,
            "mass_note": "laplaceAt smoothSeed 0 = 3 (Lean-certified); "
                         "a4-style float corroboration in records 2718",
        },
        "D_table": {str(k): float(D[k]) for k in sorted(D)},
        "D_closed_form_checks": {str(k): bool(v)
                                 for k, v in checks.items()},
        "sliver_convention": {
            "rule": "neighbor-cell iv sup x 8 x width on (0, 1/4096]",
            "safety": SLIVER_SAFETY,
            "worst_observed_fraction": worst_sliver,
        },
        "method_notes": [
            "sigma eliminated by endpoint maxima per factor",
            "continuum cover by INTERVAL cells everywhere: every factor "
            "is bounded at its cell-worst point (MQ at endpoint max, Psi "
            "at closest approach with the mass-piece floor), so the cell "
            "value is a sound sup; no Lipschitz/derivative machinery "
            "(the earlier max-derivative dPsi inflated the tail by 1e10: "
            "removed)",
            "correction envelope carries the FULL owner node list in "
            "every product and c_z denominator (only +-1 nodes "
            "contribute terms), matching the sampled cardinal object",
            "tail: geometric ladder x1.05 to 1e4 both signs (step sets "
            "the (hi/lo)^k* Psi-slack: 1.05^12 = 1.8); compact zone "
            "0.05 cells with 0.005 refinement near active heights",
            "coverage: envelope must dominate the L300 pipeline cardinal "
            "on the 2033-style grid (relative 1e-9 pad): convention "
            "bugcatch",
            "repricing lanes: PAIR uses the certified (T=2^(N+1), q*(T)) "
            "pair (contraction premise priced at q*^2n); KEEP-Q keeps "
            "the sampled 2^-14 contraction and prices certified C4*C2 "
            "against the 2033 F_max budget",
        ],
        "rows": rows_out,
        "nonclaims": [
            "model-grade owner constants (stored binary64 nodes); the "
            "node-radius transfer brick stays open",
            "numeric certified enclosures, not Lean theorems; the Lean "
            "forall-strip absorption is a separate brick",
            "no producer GO, no map-103 reopening, no SourceRH, no RH "
            "claim",
        ],
        "provenance": {
            "script": "scripts/p3_certified_strip_constants_2720.py",
            "script_sha256": hashlib.sha256(
                Path(__file__).read_bytes()).hexdigest(),
            "producer_modules": {
                "fourpoint_actual_owner_1980.py": hashlib.sha256(
                    (ROOT / "scripts"
                     / "fourpoint_actual_owner_1980.py").read_bytes()
                ).hexdigest(),
                "fourpoint_powered_seed_1981.py": hashlib.sha256(
                    (ROOT / "scripts"
                     / "fourpoint_powered_seed_1981.py").read_bytes()
                ).hexdigest(),
            },
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    log("wrote %s (status=%s)" % (OUTPUT.name, status))


class Row_:
    """Minimal row container (owner/targets/values from the 1980 builder)."""

    def __init__(self, cand):
        self.cand = cand
        self.rho = complex(cand["re"], cand["gamma"])
        owner, targets, radius, known = op.build_owner(self.rho, cand["N"])
        self.owner = owner
        self.targets = targets
        self.radius = radius
        self.H = 3.0 + abs(self.rho)
        self.values = [op.target_value(self.rho, z) for z in owner]
        self.base_values = [1.0 + 0j] * len(targets)
        self.corr_nodes = [z for z, v in zip(owner, self.values)
                           if abs(v) > 0.5]
        self.corr_y = [1.0 if v.real > 0 else -1.0
                       for z, v in zip(owner, self.values) if abs(v) > 0.5]
        self.base_nodes = list(targets)


if __name__ == "__main__":
    main()
