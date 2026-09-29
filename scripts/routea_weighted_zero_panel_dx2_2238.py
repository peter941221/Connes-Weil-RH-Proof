"""Record 2238: dx^2-law panel allowance with measured zero-free cells.

The 2234 envelope allows, per channel, a panel term

    panel = L * (2 a_max) * dx / 4

with L a global Lipschitz majorant of the weighted integrand
g = |h_k| e^{sigma x} (h_k = F for M0, F'' for D2).  That O(dx) form is
the sharp bound for a general Lipschitz integrand; the composite-trapezoid
identity on the uniform step-dx grid (two integrations by parts, Stieltjes
form) instead gives

    T - I = (dx^2/12) sum_p Delta_p
            - (dx^2/2) sum_p int_0^1 B_2(t) dg'(x_p + t dx),

with Delta_p the one-sided increment of g' across cell p.  The Delta sum
telescopes:

    sum_p Delta_p = g'(x_N) - g'(x_0) + sum_{node kinks} J,

and g'(+-a_max) = 0 exactly (the phi support, extended by zero at |u| = 1,
has all derivatives zero there), so every surviving kink rate is dx^2:

    |T - I| <= (dx^2/12) (sum_{node kinks} J + TV(g')),
    TV(g')  <= int |g''| + sum_{all kinks} J,
    J       <= 2 |h_k'(x*)| e^{sigma x*} <= 2 e^{sigma a} m_{k+1}.

This record charges the per-cell worst case: a cell not certified
zero-free carries

    panel_risk_cell = (dx^2/12) (dx M_k(sigma) + 2 e^{sigma a} m_{k+1}),

covering the interior-kink TV term and the cell's share of int |g''|;
zero-free cells are covered by the global (2 a_max) M_k term:

    panel = (dx^2 / 12) [ (2 a_max) M_k(sigma)
                          + N_risk (dx M_k(sigma) + 2 e^{sigma a} m_{k+1}) ]

where M_k(sigma) = e^{sigma a} (m_{k+2} + 2 sigma m_{k+1} + sigma^2 m_k)
bounds sup |g''| through the global phi^(k) majorant ladder, m_{k+1}
bounds the corner slope mass at a zero of h_k, and N_risk is the number of
cells NOT certified zero-free by the node test

    |h_k(x_p)| > dx * m_{k+1}   (a zero in [x_p, x_{p+1}] forces
                                 |h_k(x_p)| <= dx sup_cell |h_k'|),

evaluated on the committed 2234 chunk arrays with a 1e-9 guard on both
sides (the stored values are outward to ~1e-15 relative).  The order-4
majorant uses the same simple rule as 2234's ladder, applied to the Bell
expansion of phi^(4): every product u^{2j} q^{-m} e^{-K/q} with m <= 8
is bounded by e^{-K}.

Measured outcome: the classification wall.  The stored magnitudes have
medians |F| ~ 1.5e-6, |F''| ~ 4.7e-3 (base) and median |F''| ~ 1.65
(corr), while the node-test threshold dx * m_{k+1} stays >= 0.1 for the
M0 channel and >= 700 for base_D2: 76-87% of cells are risk cells.  The
dx^2-law therefore delivers only ~1.8x over the 2234 panel here, and the
record registers the composite-EM reading (drop N_risk via a certified
real-zero count Z; a numpy scan finds Z = 0 with deepest interior dips
2.5e-12 / 4.9e-9 on the base channels) as the instrument that removes
the wall, projecting panels ~1.6e3..1.8e3x below the 2234 values.

Modes (environment):
  MODE=recon   -> results/2238_panel_recon.json
  MODE=reduce  -> results/2238_panel_dx2_reprice.json

The reprice stacks on the 2237 certified generation radius when present
(results/2237_generation_certificate.json), else on the 2236 solve floor.
"""
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
UP = lambda v: math.nextafter(v, math.inf)
SIGNED_MARGIN = 1675397327895.099
SCREEN_2197 = {"C_upper": 77444.14398633591, "B_upper": 3057372.2573045553,
               "tail_upper": 3691230708.643563,
               "tail_over_margin": 0.0022031972041408675}


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


def majors(a):
    """sup |phi^(k)| bounds, k <= 4 (same rule as 2234's ladder)."""
    eK = math.exp(-30.0)
    K = 30.0
    c0 = eK
    c1 = (2.0 * K / a) * eK
    c2 = eK * (10.0 * K + 4.0 * K * K) / (a * a)
    c3 = eK * (72.0 * K + 30.0 * K * K + 8.0 * K ** 3) / (a ** 3)
    c4 = eK * (696.0 * K + 780.0 * K ** 2 + 360.0 * K ** 3
               + 16.0 * K ** 4) / (a ** 4)
    return c0, c1, c2, c3, c4


def ladder(fam, coef):
    m = [0.0] * 5
    for (a, th), c in zip(fam, coef):
        cs = majors(a)
        w = abs(complex(c))
        for j in range(5):
            s = 0.0
            for i in range(j + 1):
                s += math.comb(j, i) * abs(th) ** i * cs[j - i]
            m[j] += w * s
    return m


def load_arrays():
    o34 = _load("o34a", "routea_weighted_zero_direct_product_outward_2234.py")
    s97 = _load("s97a", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = o34.build_construction()
    nx = s97.NX
    dx = (2.0 * a_max) / (nx - 1)
    U = np.zeros((4, nx))
    for k in range(12):
        z = np.load(R / f"2234_chunk_{k}.npz")
        U[:, int(z["i0"]):int(z["i1"])] = z["U"]
    return fam, base, corr, a_max, dx, U


def recon():
    fam, base, corr, a_max, dx, U = load_arrays()
    out = {"record": 2238, "part": "recon", "a_max": a_max, "dx": dx,
           "channels": {}}
    ref = {"base_M0": 1.8076571806532764, "base_D2": 11693.314770969451,
           "corr_M0": 2862.4920101295183, "corr_D2": 17018191.948288612}
    for name, coef, idx in (("base_M0", base, 0), ("base_D2", base, 1),
                            ("corr_M0", corr, 2), ("corr_D2", corr, 3)):
        m = ladder(fam, coef)
        k = 0 if name.endswith("M0") else 2
        thr = dx * m[k + 1] * (1.0 + 1e-9)
        u = U[idx]
        ok = (u[:-1] * (1.0 - 1e-9) > thr) & (u[1:] * (1.0 - 1e-9) > thr)
        nrisk = int((~ok).sum())
        panels = {}
        for sigma in (0.5, 1.0):
            g = math.exp(sigma * a_max)
            Mk = g * (m[k + 2] + 2.0 * sigma * m[k + 1] + sigma ** 2 * m[k])
            panels[str(sigma)] = up_many(
                (dx * dx / 12.0) * ((2.0 * a_max) * Mk
                                    + nrisk * (dx * Mk + 2.0 * g * m[k + 1])),
                4)
        out["channels"][name] = {
            "majorants": m, "threshold": thr, "n_risk": nrisk,
            "cells": int(u.shape[0] - 1),
            "median_abs": float(np.median(u)),
            "panel_new": panels, "panel_2234": ref[name],
            "ratio_2234_over_new_sigma1": ref[name] / panels["1.0"]}
    out["status"] = "PANEL-DX2-RECON"
    (R / "2238_panel_recon.json").write_text(json.dumps(out, indent=2) + "\n",
                                             encoding="utf-8")
    print(json.dumps({"status": out["status"], "channels": {
        k: {"n_risk": v["n_risk"], "median": v["median_abs"],
            "ratio": v["ratio_2234_over_new_sigma1"]}
        for k, v in out["channels"].items()}}, indent=2), flush=True)


_TABLE = None


def panel_table():
    """Per-channel panel inputs from the recon table (cached)."""
    global _TABLE
    if _TABLE is not None:
        return _TABLE
    rec = json.loads((R / "2238_panel_recon.json").read_text(encoding="utf-8"))
    _, _, _, a_max, dx, _ = load_arrays()
    table = {}
    for name in ("base_M0", "base_D2", "corr_M0", "corr_D2"):
        m = rec["channels"][name]["majorants"]
        nrisk = rec["channels"][name]["n_risk"]
        k = 0 if name.endswith("M0") else 2
        table[name] = (m, k, nrisk, a_max, dx)
    _TABLE = table
    return table


def panel_new(name, sigma):
    m, k, nrisk, a_max, dx = panel_table()[name]
    g = math.exp(sigma * a_max)
    Mk = g * (m[k + 2] + 2.0 * sigma * m[k + 1] + sigma ** 2 * m[k])
    return up_many((dx * dx / 12.0) * ((2.0 * a_max) * Mk
                                       + nrisk * (dx * Mk + 2.0 * g * m[k + 1])),
                   4)


def reduce_worker():
    rp = _load("rp2235h", "routea_weighted_zero_direct_product_reprice_2235.py")
    o34 = _load("o34h", "routea_weighted_zero_direct_product_outward_2234.py")
    s97 = _load("s97h", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = o34.build_construction()
    cert = None
    rpath = R / "2237_generation_certificate.json"
    if rpath.exists():
        cert = json.loads(rpath.read_text(encoding="utf-8"))
        radii = {"r_base": cert["radius"]["r_base"],
                 "r_corr": cert["radius"]["r_corr"]}
        radius_source = "2237 certified generation channel"
    else:
        scales = rp.system_radii()
        radii = {"r_base": scales["r_base_floor"],
                 "r_corr": scales["r_corr_floor"]}
        radius_source = "2236 solve floor"
    prev = json.loads((R / "2234_direct_product_outward.json")
                      .read_text(encoding="utf-8"))
    d_sigma = 0.01
    cover1 = math.exp(a_max * d_sigma)
    best = None
    rows = []
    for row34 in prev["sigma_rows"]:
        sigma = row34["sigma"]
        j = int(round(sigma * 100))
        sig = json.loads((R / f"2234_sigma_{j}.json").read_text(encoding="utf-8"))
        v = sig["values"]
        pb = panel_new("base_M0", sigma)
        pb2 = panel_new("base_D2", sigma)
        pc = panel_new("corr_M0", sigma)
        pc2 = panel_new("corr_D2", sigma)
        eb = o34.coeff_inflation(base, fam, s97.K, a_max, sigma,
                                 radii["r_base"], 0)
        eb2 = o34.coeff_inflation(base, fam, s97.K, a_max, sigma,
                                  radii["r_base"], 2)
        ec = o34.coeff_inflation(corr, fam, s97.K, a_max, sigma,
                                 radii["r_corr"], 0)
        ec2 = o34.coeff_inflation(corr, fam, s97.K, a_max, sigma,
                                  radii["r_corr"], 2)
        mb = up_many(up_many((v["base_M0"] + pb) * (1.0 + eb), 3) * cover1, 3)
        db = up_many(up_many((v["base_D2"] + pb2) * (1.0 + eb2), 3) * cover1,
                     3)
        mc = up_many(up_many((v["corr_M0"] + pc) * (1.0 + ec), 3) * cover1, 3)
        dc = up_many(up_many((v["corr_D2"] + pc2) * (1.0 + ec2), 3) * cover1,
                     3)
        tp2 = up_many((2.0 * math.pi) ** 2, 3)
        c1 = up_many(up_many(db * mc, 3) / tp2, 3)
        c2 = up_many(up_many(dc * mb, 3) / tp2, 3)
        out = {"sigma": sigma, "base_M0": mb, "base_D2": db, "corr_M0": mc,
               "corr_D2": dc, "panel_base": pb, "panel_base_D2": pb2,
               "panel_corr": pc, "panel_corr_D2": pc2,
               "coeff_infl_base": eb, "coeff_infl_base_D2": eb2,
               "coeff_infl_corr": ec, "coeff_infl_corr_D2": ec2,
               "C_channel_a": c1, "C_channel_b": c2, "C_upper": min(c1, c2)}
        rows.append(out)
        if best is None or out["C_upper"] > best["C_upper"]:
            best = out
    assert best is not None
    xi2 = math.pi / 6.0
    kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
    xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    mult = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)
    b_upper = up_many(up_many((2.0 * math.pi) ** 2, 3) * best["C_upper"], 3)
    tail_upper = up_many(up_many(4.0 * mult, 3) * b_upper, 3)
    rec = json.loads((R / "2238_panel_recon.json").read_text(encoding="utf-8"))
    result = {
        "record": 2238,
        "status": ("PANEL-DX2-REPRICE-VIABLE" if tail_upper <= SIGNED_MARGIN
                   else "PANEL-DX2-REPRICE-OPEN"),
        "lever": "dx^2-law panel: Euler-Maclaurin measure form on measured "
                 "zero-free cells, global phi^(k) majorant ladder m0..m4",
        "radius": radii,
        "radius_source": radius_source,
        "panel_2238_sigma1": {k: v["panel_new"]["1.0"]
                              for k, v in rec["channels"].items()},
        "panel_2234_sigma1": {k: v["panel_2234"]
                              for k, v in rec["channels"].items()},
        "n_risk": {k: v["n_risk"] for k, v in rec["channels"].items()},
        "binding_row": best,
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_upper / SIGNED_MARGIN},
        "comparison_2197": SCREEN_2197,
        "comparison_2234": {"C_upper_2234": prev["screen"]["C_upper"],
                            "tail_over_margin_2234":
                            prev["screen"]["tail_upper_over_margin"],
                            "C_repricing_factor":
                            prev["screen"]["C_upper"] / best["C_upper"]},
        "drift": {k: rp.sig_drift(k) for k in
                  ("base_M0", "base_D2", "corr_M0", "corr_D2")},
        "inflation_over_2197": {"C": best["C_upper"] / SCREEN_2197["C_upper"],
                                "tail": tail_upper
                                / SCREEN_2197["tail_upper"]},
        "finding_classification_wall": {
            "node_test": "|h_k(x_p)| > dx * m_{k+1} (both endpoints, 1e-9 "
                         "guard both sides on the stored outward values)",
            "medians": {k: v["median_abs"]
                        for k, v in rec["channels"].items()},
            "thresholds": {k: v["threshold"]
                           for k, v in rec["channels"].items()},
            "consequence": "76-87% of cells fail the test; the corner mass "
                           "is bounded by the global m_{k+1}, which is "
                           "1e3..1e6x above the local slope scale",
            "next_instrument": "local Bell-level probes P0..P4 with "
                               "directed node bounds; the leftover cascade "
                               "dx^(j+1) m_{j+1} then shrinks by ~dx per "
                               "measured level (corr_D2 needs P4 local: its "
                               "dx^2 m4 floor is 1715 vs median |F''| 1.65)",
        },
        "nonclaims": [
            "the risk-cell count is measured from the committed 2234 chunk "
            "arrays with a 1e-9 guard; the corner mass still uses a global "
            "majorant (the classification wall)",
            "the order-4 majorant follows the same validity rule as 2234's "
            "ladder (master bound sup q^-m e^-K/q <= e^-K, m <= 8 here)",
            "the coefficient radii inherit the 2237 certificate",
            "complete-owner transfer and the signed producer margin remain "
            "open",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_panel_dx2_2238.py",
            "sigma_sums": "results/2234_sigma_*.json",
            "chunks": "results/2234_chunk_*.npz (local-only)",
            "radius": radius_source,
        },
    }
    (R / "2238_panel_dx2_reprice.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "C_upper": best["C_upper"],
                      "tail_over_margin": tail_upper / SIGNED_MARGIN,
                      "C_factor_vs_2234":
                          prev["screen"]["C_upper"] / best["C_upper"],
                      "binding_sigma": best["sigma"]}, indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "recon")
    if mode == "recon":
        recon()
    elif mode == "reduce":
        reduce_worker()
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()