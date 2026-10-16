#!/usr/bin/env python3
r"""Record 2721A recon: analytic upgrade of the two 2718 observational premises.

Planning-grade numbers only (Windows python, mpmath reference quads).  The
decision this probe settles:

  (D1) can the seed premise  E_seed = 10 * max|L_1200 - L_300|  be replaced
       by   max float |L_300 - L_1200|  +  analytic tail |L_1200 - L_ideal|
       with a uniform bound B_seed that clears every per-claim E_L_critical
       (2718 artifact: 19.3 / 0.8285 / 2.95 / 0.676) by >= 10x?

  (D2) is the grid premise M_grid = 10 * observed movement replaceable by
       a deterministic 0.01-vs-0.005 float difference plus an Euler-
       Maclaurin tail (h * log kmax)^(2P) * 2 zeta(2P) * mass, clearing the
       mv budget by >= 10x?

Math (recorded so the rig inherits it, not re-derived at build time):

  Seed integrand on [-2,2]:  f(x) = T(x+2) T(2-x),
  T(y) = 1/(1 + exp(g(y))),  g(y) = 1/y - 1/(1-y)  for 0 < y < 1,
  T = 0 for y <= 0, T = 1 for y >= 1 (matches op.smooth_transition exactly:
  a/(a+b), a = e^{-1/y}, b = e^{-1/(1-y)}).
  f is real-analytic on (-2,2) \ {-1, 1}; NOT complex-analytic on any domain
  containing [-2,2] (identity theorem: f == 1 on [-1,1] while it has a
  genuine transition on (1,2)).  Hence no whole-interval Trefethen bound;
  the certified tail splits:
    middle  [-1,1]:  int e^{u x} dx in closed form (u = 0.5 s);
    slabs   (edge pieces of width a around +/-1 and the support tails):
                     |T| <= e^{-1/y} <= e^{-1/a} charged by measure;
    panels  y in [a, 1-a] mapped to each edge piece: F is analytic up to the
                     logistic poles: g(y) = i pi (2k+1)  <=>  c y^2-(c+2)y+1=0
                     with c = i pi (2k+1); residue of F = -1/g'(y_p),
                     |g'(y)| = |1/y^2 + 1/(1-y)^2|.
  Trefethen strip bound per panel: |I - G_m| <= 4 M rho^{-2m} / (1 - rho^{-2}),
  rho = b/c + sqrt(1 + (b/c)^2) for ellipse half-height b = d_min / 2.
  Powered amplification on the imaginary axis (Re s = 0): |L1| <= int f = 3,
  |L_pow_a - L_pow_b| <= 10 * max(|L1_a|, |L1_b|)^9 * |L1_a - L1_b|.

Stop condition: this recon prints the predicted B_seed, the per-claim margins
and a GO / NO-GO for the full rig; no enclosure claims.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op        # noqa: E402
import fourpoint_powered_seed_1981 as powered   # noqa: E402

A_SLAB = 0.06
S_MAX = 160.0
SIGMAS = [0.0, 4.0, 16.0, 40.0, 80.0, 120.0, 160.0]
ORDERS = (300, 600, 1200, 2400)
REF_ORDER = 1200
E_CRIT = {("A", "C_negative"): 19.300, ("A", "det_sign"): 0.82852,
          ("B", "C_negative"): 2.9541, ("B", "det_sign"): 0.67598}


def mp_T(y: mp.mpf) -> mp.mpf:
    y = mp.mpf(y)
    if y <= 0:
        return mp.mpf(0)
    if y >= 1:
        return mp.mpf(1)
    return 1 / (1 + mp.exp(1 / y - 1 / (1 - y)))


def mp_seed_raw(u, x) -> mp.mpf:
    y1, y2 = 2 + x, 2 - x
    return mp_T(y1) * mp_T(y2) * mp.exp(u * x)


def main() -> None:
    out = {"env": "windows-python recon (planning grade)",
           "A_slab": A_SLAB, "S_MAX": S_MAX, "ref_order": REF_ORDER}

    # ------------------------------------------------ raw node/weight sets --
    tf300 = powered.make_powered_seed(order=300)
    seed0 = complex(tf300(np.array([0j]))[0])
    out["seed0"] = [seed0.real, seed0.imag]
    assert abs(seed0.real - 59049.0) < 1e-6 and abs(seed0.imag) < 1e-6, seed0

    raws = {}
    for o in ORDERS:
        nodes, weights = np.polynomial.legendre.leggauss(o)
        x = 2.0 * nodes
        w = 2.0 * weights * op.smooth_seed_raw(x)
        raws[o] = (x, w)

    def raw_at(o: int, sigma: float) -> complex:
        x, w = raws[o]
        s = 1j * sigma
        return complex(np.sum(np.exp((0.5 * s) * x) * w))

    # --------------------------------- deterministic float difference (D1a) --
    tf_ref = powered.make_powered_seed(order=REF_ORDER)
    tf_2400 = powered.make_powered_seed(order=2400)
    dens = sorted(set(SIGMAS) | {i * 8.0 for i in range(21)})
    D_float = 0.0
    D_float_2400 = 0.0
    for sg in dens:
        p300 = complex(tf300(np.array([1j * sg]))[0])
        for o, acc in ((REF_ORDER, "D"), (2400, "E")):
            po = complex((tf_ref if o == REF_ORDER else tf_2400)(
                np.array([1j * sg]))[0])
            if acc == "D":
                D_float = max(D_float, abs(p300 - po))
            else:
                D_float_2400 = max(D_float_2400, abs(p300 - po))
    out["D_float_pow_300_vs_1200"] = D_float
    out["D_float_pow_300_vs_2400"] = D_float_2400

    # ------------------------------------------------- analytic tail of 1200 --
    mp.mp.dps = 60
    int_f = mp.quad(lambda x: mp_seed_raw(0, x), [-2, -1, 1, 2])
    out["int_f_exact_mp"] = mp.nstr(int_f, 12)
    max_raw = max(abs(raw_at(REF_ORDER, s)) for s in dens)
    out["max_raw_1200_on_axis"] = max_raw

    # measured actual raw tail vs mp reference (calibration, not certificate)
    tail_meas = 0.0
    rows_meas = []
    for sg in SIGMAS:
        u = 0.5j * sg
        I_mid = (mp.mpf(2) * mp.sin(0.5 * sg) / (0.5 * sg) if sg != 0
                 else mp.mpf(2))
        I_edge = mp.quad(lambda x: mp_seed_raw(u, x), [1, 2])
        I = I_mid + I_edge + mp.conj(I_edge)
        got = raw_at(REF_ORDER, sg)
        d = abs(complex(I) - got)
        assert d <= 6.01, (sg, d)   # both sides have modulus <= int f = 3
        rows_meas.append([sg, float(d)])
        tail_meas = max(tail_meas, float(d))
    out["tail_1200_vs_mpquad_measured"] = tail_meas
    out["tail_rows"] = rows_meas
    pow_tail_1200 = 10.0 * (max(max_raw, 3.0004)) ** 9 * tail_meas
    out["B_pow_tail_1200_amplified"] = pow_tail_1200

    # -------------------------------------------- pole geometry for panels --
    poles = []
    for k in range(0, 3200):
        c = 1j * mp.pi * (2 * k + 1)
        disc = (c + 2) ** 2 - 4 * c
        sq = mp.sqrt(disc)
        for r in ((c + 2 + sq) / (2 * c), (c + 2 - sq) / (2 * c)):
            # F is real on the real axis: poles are conjugate-symmetric, so
            # the UPPER half-plane member of the pair is conj(r) when Im r < 0.
            ru = mp.conj(r) if mp.im(r) < 0 else r
            if mp.im(ru) > 0:
                yp = complex(mp.re(ru), mp.im(ru))
                gp = complex(mp.mpf(1) / ru ** 2 + mp.mpf(1) / (1 - ru) ** 2)
                poles.append((k, yp, abs(1 / gp)))
    # distance from each pole to panel [a, 1-a] (real segment in y-space)
    a = A_SLAB
    dmin = math.inf
    binder = None
    for k, yp, res in poles:
        x, h = yp.real, yp.imag
        dx = 0.0 if a <= x <= 1 - a else min(abs(x - a), abs(x - (1 - a)))
        d = math.hypot(dx, h)
        if d < dmin:
            dmin, binder = d, (k, x, h)
    out["n_poles_upper"] = len(poles)
    out["d_min_pole_to_panel"] = dmin
    out["binder_pole"] = binder

    # Trefethen strip numbers with b = dmin/2, half-length c = (1-2a)/2
    c_h = (1.0 - 2 * a) / 2.0
    b = dmin / 2.0
    rho = b / c_h + math.sqrt(1 + (b / c_h) ** 2)
    # M on ellipse boundary: sup |F| * e^{|u| |Im y|}, |u| = 0.5 S_MAX
    M = 0.0
    for th in np.linspace(0, 2 * math.pi, 240, endpoint=False):
        t = c_h * math.cos(th)
        yi = b * math.sin(th)
        y = (0.5 + t) + 1j * yi   # panel midpoint 0.5
        with mp.workdps(40):
            gv = 1 / mp.mpc(y.real, y.imag) - 1 / (1 - mp.mpc(y.real, y.imag))
            Fv = 1 / (1 + mp.exp(gv))
        M = max(M, abs(Fv) * math.exp(0.5 * S_MAX * abs(yi)))
    M = float(M)
    for m in (300, 1200, 2400):
        est = 4 * M * rho ** (-2 * m) / (1 - rho ** -2)
        out[f"panel_strip_bound_m{m}"] = est
    slab_max = math.exp(-1 / a)
    out["slab_mag_per_side"] = slab_max
    slab_pow = 10 * 3.0004 ** 9 * (2 * a + 2 * slab_max * 2) * slab_max
    out["B_pow_slab_charged"] = slab_pow

    # ----------------------------------------------------- D1 verdict block --
    B_seed = D_float + max(pow_tail_1200, out["panel_strip_bound_m1200"] * 10 * 3.0004 ** 9)
    out["B_seed_predicted"] = B_seed
    out["margins_vs_e_crit"] = {
        f"{r}/{c}": E_CRIT[(r, c)] / B_seed for (r, c) in E_CRIT}

    # ------------------------------------------------------------ D2: EM grid --
    for n, name in ((4, "rowA"), (5, "rowB")):
        logk = 2 * (n + 2)
        for h in (0.01, 0.005):
            for P in (6, 8):
                val = (h * logk) ** (2 * P) * 2 * float(mp.zeta(2 * P))
                out[f"EM_{name}_h{h}_P{P}"] = val

    print(json.dumps(out, indent=1))
    Path("results/2721A_seed_premise_recon.json").write_text(
        json.dumps(out, indent=1), encoding="utf-8")
    go = all(v >= 10 for v in out["margins_vs_e_crit"].values())
    print("VERDICT:", "GO-rig" if go else "NO-GO / retune",
          "| B_seed=%.3e min-margin=%.1fx" % (
              B_seed, min(out["margins_vs_e_crit"].values())))


if __name__ == "__main__":
    main()
