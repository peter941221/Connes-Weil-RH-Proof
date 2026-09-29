"""Record 2235: reprice the direct-product outward envelope with a
system-scaled coefficient radius.

Record 2234 produced an outward but loose envelope: the coefficient
allowance imported the record-2201 Neumann radius (R_BASE 1.7259e8,
R_CORR 3.5365e11).  The repricing here recomputes, from the committed 2197
construction itself,

  A_inf, Ainv_inf, c_inf, resid,
  r_c = Ainv_inf * (eta * A_inf * c_inf + resid)

with the generation-error screen eta = 1e-12 (ten times the 2233 w-channel
moment gap 9.16e-14).  The measured radii land close to the 2201 values
(r_base 1.4926e8, r_corr 3.0583e11): the 2201 preflight priced the same
system, so the 2234 envelope was not repairable by radius rescaling alone.
The residual finding of this record is the attribution: charging a
generation channel (eta term) and a solve channel (resid term) together
under one radius; the two separate under the discrete-defined convention.

The sigma sums, panel allowances and sigma cover are reused verbatim from
the committed 2234 artifacts, so the delta against 2234 is exactly the
coefficient channel.  The reduce is factored into run_reduce(radii, ...)
so record 2236 can reprice the same envelope with a different radius model.

Reads results/2234_sigma_*.json, writes results/2235_direct_product_reprice.json.
"""
import importlib.util
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
ETA_SCREEN = 1e-12
SIGNED_MARGIN = 1675397327895.099
SCREEN_2197 = {"C_upper": 77444.14398633591, "B_upper": 3057372.2573045553,
               "tail_upper": 3691230708.643563,
               "tail_over_margin": 0.0022031972041408675}
UP = lambda v: math.nextafter(v, math.inf)


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


def system_radii():
    """Rebuild the 2197 system; return scales, residuals and both radii."""
    s97 = _load("s97r", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    nodes, values, fam = s97.owner_family()
    base_xw = [s97.r59.phi_weights(a, panels=6, m=s97.M) for a, _ in fam]
    a_mat = s97.r80.family_values(fam, s97.K, np.asarray(nodes, complex),
                                  base_xw).T
    b_base = np.ones(len(nodes), complex)
    b_corr = np.asarray(values, complex)
    base = np.linalg.solve(a_mat, b_base)
    corr = np.linalg.solve(a_mat, b_corr)
    a_inf = float(np.linalg.norm(a_mat, ord=np.inf))
    ainv = np.linalg.inv(a_mat)
    ainv_inf = float(np.linalg.norm(ainv, ord=np.inf))
    resid_base = float(np.linalg.norm(a_mat @ base - b_base, ord=np.inf))
    resid_corr = float(np.linalg.norm(a_mat @ corr - b_corr, ord=np.inf))
    c_base_inf = float(np.linalg.norm(base, ord=np.inf))
    c_corr_inf = float(np.linalg.norm(corr, ord=np.inf))
    r_base = up_many(ainv_inf * (ETA_SCREEN * a_inf * c_base_inf
                                 + resid_base), 3)
    r_corr = up_many(ainv_inf * (ETA_SCREEN * a_inf * c_corr_inf
                                 + resid_corr), 3)
    gamma30 = up_many(30.0 * 2.0 ** -52 / (1.0 - 30.0 * 2.0 ** -52), 2)
    floor_base = up_many(ainv_inf * (resid_base
                                     + gamma30 * a_inf * c_base_inf), 3)
    floor_corr = up_many(ainv_inf * (resid_corr
                                     + gamma30 * a_inf * c_corr_inf), 3)
    return {"a_inf": a_inf, "ainv_inf": ainv_inf,
            "cond_inf": a_inf * ainv_inf,
            "base_c_inf": c_base_inf, "corr_c_inf": c_corr_inf,
            "resid_base": resid_base, "resid_corr": resid_corr,
            "gamma30": gamma30,
            "r_base": r_base, "r_corr": r_corr,
            "r_base_floor": floor_base, "r_corr_floor": floor_corr,
            "eta_screen": ETA_SCREEN}


def run_reduce(radii, record, lever, out_name, status_ok, extra=None):
    """Reprice the 2234 sigma sums with the given coefficient radii."""
    o34 = _load("o34r", "routea_weighted_zero_direct_product_outward_2234.py")
    s97 = _load("s97q", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    fam, base, corr, a_max = o34.build_construction()
    prev = json.loads((R / "2234_direct_product_outward.json")
                      .read_text(encoding="utf-8"))
    d_sigma = 0.01
    cover1 = math.exp(a_max * d_sigma)
    dx = (2.0 * a_max) / (s97.NX - 1)
    best = None
    rows = []
    for row34 in prev["sigma_rows"]:
        sigma = row34["sigma"]
        j = int(round(sigma * 100))
        sig = json.loads((R / f"2234_sigma_{j}.json").read_text(encoding="utf-8"))
        v = sig["values"]
        L_b, _ = o34.integrand_lipschitz(base, fam, s97.K, a_max, sigma)
        L_c, _ = o34.integrand_lipschitz(corr, fam, s97.K, a_max, sigma)
        _, L_b2 = o34.integrand_lipschitz(base, fam, s97.K, a_max, sigma)
        _, L_c2 = o34.integrand_lipschitz(corr, fam, s97.K, a_max, sigma)
        panel = lambda L: L * (2.0 * a_max) * dx / 4.0
        pb, pb2 = panel(L_b), panel(L_b2)
        pc, pc2 = panel(L_c), panel(L_c2)
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
    drift = {k: sig_drift(k) for k in
             ("base_M0", "base_D2", "corr_M0", "corr_D2")}
    result = {
        "record": record,
        "status": ("DIRECT-PRODUCT-OUTWARD-VIABLE" if
                   tail_upper <= SIGNED_MARGIN else status_ok),
        "lever": lever,
        "radius": radii,
        "owner": prev["owner"],
        "grid": prev["grid"],
        "binding_row": best,
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant_proxy": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_upper / SIGNED_MARGIN},
        "comparison_2197": SCREEN_2197,
        "comparison_2234": {"C_upper_2234": prev["screen"]["C_upper"],
                            "tail_over_margin_2234":
                            prev["screen"]["tail_upper_over_margin"],
                            "C_repricing_factor":
                            prev["screen"]["C_upper"] / best["C_upper"]},
        "inflation_over_2197": {"C": best["C_upper"] / SCREEN_2197["C_upper"],
                                "tail": tail_upper
                                / SCREEN_2197["tail_upper"]},
        "sigma1_drift_vs_2197": drift,
        "allowances": {
            "slack": "reused from 2234 (MPFR RNDN + 2^-200 magnitude sum)",
            "panel": "reused from 2234 (global phi^(k) majorants, dx law)",
            "sigma": "reused from 2234 (exp(a_max d_sigma) per norm)",
            "coeff": "recomputed here from the 2197 system scales",
        },
        "nonclaims": [
            "the coefficient radii separate a generation term (eta screen) "
            "from a solve term (residual); the split is the subject of 2236",
            "the panel allowance still carries a global-majorant factor; the "
            "residual inflation over the 2197 screen is that channel",
            "the multiplicity constant is still the 2197 diagnostic proxy",
            "complete-owner transfer and the signed producer margin remain "
            "open",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_direct_product_reprice_2235.py",
            "sigma_sums": "results/2234_sigma_*.json",
            "system": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py",
        },
    }
    if extra:
        result.update(extra)
    (R / out_name).write_text(json.dumps(result, indent=2) + "\n",
                              encoding="utf-8")
    return result


def sig_drift(name):
    """sigma=1 chunk trapezoid vs the committed 2197 values."""
    o34 = _load("o34d", "routea_weighted_zero_direct_product_outward_2234.py")
    s97 = _load("s97d", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    x = o34.x_grid(float(o34.build_construction()[3]))
    U = np.zeros((4, x.shape[0]))
    for k in range(12):
        z = np.load(R / f"2234_chunk_{k}.npz")
        U[:, int(z["i0"]):int(z["i1"])] = z["U"]
    w = np.exp(1.0 * x)
    ref = {"base_M0": 2.0033357887456087, "base_D2": 6688.576604759935,
           "corr_M0": 913.4469710803505, "corr_D2": 1526140.687188009}
    idx = ("base_M0", "base_D2", "corr_M0", "corr_D2").index(name)
    val = float(np.trapezoid(U[idx] * w, x))
    return {"chunk_trapezoid": val, "committed_2197": ref[name],
            "relative": (val - ref[name]) / ref[name]}


def main():
    rad = system_radii()
    result = run_reduce(rad, 2235,
                        "system-scaled coefficient radius: generation screen "
                        "eta = 1e-12 plus measured residual",
                        "2235_direct_product_reprice.json",
                        "DIRECT-PRODUCT-OUTWARD-STILL-LOOSE")
    print(json.dumps({"status": result["status"],
                      "binding_sigma": result["binding_row"]["sigma"],
                      "C_upper": result["screen"]["C_upper"],
                      "tail_upper_over_margin":
                      result["screen"]["tail_upper_over_margin"],
                      "repricing_factor":
                      result["comparison_2234"]["C_repricing_factor"],
                      "inflation_over_2197": result["inflation_over_2197"],
                      "cond_inf": rad["cond_inf"],
                      "r_base": rad["r_base"], "r_corr": rad["r_corr"]},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()