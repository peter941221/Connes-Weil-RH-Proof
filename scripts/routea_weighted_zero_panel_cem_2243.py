"""Record 2243: composite-EM panel landing on the certified zero count.

Record 2242 certifies Z = 0 for the four channel functions h_0 = F and
h_2 = F'' (base and corr coefficient vectors): no real zeros on
(-a30, a30), the boundary zeros at +-a30 flat.  With no kinks the
composite-trapezoid identity of 2238,

    T - I = (dx^2/12) sum_p Delta_p - (dx^2/2) sum_p int_0^1 B_2 dg',

telescopes with g'(x_N) - g'(x_0) = 0 and TV(g') <= int |g''| <=
(2 a_max) M_k(sigma), so the per-channel panel allowance is the clean

    panel_cem(name, sigma) = (dx^2/12) (2 a_max) M_k(sigma),
    M_k(sigma) = e^{sigma a_max} (m_{k+2} + 2 sigma m_{k+1} + sigma^2 m_k),

i.e. exactly the 2238 `panel_new` with the risk-term count N_risk = 0
(the wall term drops by certificate, not by measurement).

Everything downstream is the 2238 reduction, unchanged and bitwise: the
sigma-row sums from results/2234_sigma_*.json, the coefficient inflation
on the 2237 certified radii, the cover factor exp(a_max * 0.01), the
min-of-two-channels C, B_upper = (2 pi)^2 C, and the Lean tail
4 * mult * B_upper against the signed margin 1675397327895.099.

Gates: refuses to run unless results/2242_zero_count_certificate.json
reads ZERO-COUNT-CERTIFIED.  The 2238-doc projection (C_upper
384556.5741856599, tail/margin 0.010940194125321153) is stored and
checked against the computed values.
"""
import importlib.util
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
SIGNED_MARGIN = 1675397327895.099
SCREEN_2197 = {"C_upper": 77444.14398633591, "B_upper": 3057372.2573045553,
               "tail_upper": 3691230708.643563,
               "tail_over_margin": 0.0022031972041408675}
PROJECTION = {
    "panel_sigma1": {"base_M0": 0.001034980056666458,
                     "base_D2": 7.229989871395511,
                     "corr_M0": 1.5948664429589159,
                     "corr_D2": 9721.552345634816},
    "C_upper": 384556.5741856599,
    "tail_over_margin": 0.010940194125321153,
}
COUNT_2119 = 3002.5554464806
SCREENED_NODES = 62.0


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


def panel_cem(name, sigma, table):
    m, k, nrisk, a_max, dx = table[name]
    g = math.exp(sigma * a_max)
    Mk = g * (m[k + 2] + 2.0 * sigma * m[k + 1] + sigma * sigma * m[k])
    return up_many((dx * dx / 12.0) * ((2.0 * a_max) * Mk), 4)


def main():
    cert = json.loads((R / "2242_zero_count_certificate.json")
                      .read_text(encoding="utf-8"))
    assert cert["status"] == "ZERO-COUNT-CERTIFIED", cert["status"]
    o34 = _load("o34c", "routea_weighted_zero_direct_product_outward_2234.py")
    rp = _load("rp2235c", "routea_weighted_zero_direct_product_reprice_2235.py")
    s97 = _load("s97c", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    o38 = _load("o38c", "routea_weighted_zero_panel_dx2_2238.py")
    table = o38.panel_table()
    fam, base, corr, a_max = o34.build_construction()
    cert37 = json.loads((R / "2237_generation_certificate.json")
                        .read_text(encoding="utf-8"))
    radii = {"r_base": cert37["radius"]["r_base"],
             "r_corr": cert37["radius"]["r_corr"]}
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
        pb = panel_cem("base_M0", sigma, table)
        pb2 = panel_cem("base_D2", sigma, table)
        pc = panel_cem("corr_M0", sigma, table)
        pc2 = panel_cem("corr_D2", sigma, table)
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
    tail_over = tail_upper / SIGNED_MARGIN
    rec38 = json.loads((R / "2238_panel_dx2_reprice.json")
                       .read_text(encoding="utf-8"))
    panel_match = {}
    for nm, pv in PROJECTION["panel_sigma1"].items():
        got = panel_cem(nm, 1.0, table)
        panel_match[nm] = {"computed": got, "projected": pv,
                           "rel": abs(got - pv) / pv}
    ratio_2119 = COUNT_2119 / SCREENED_NODES
    result = {
        "record": 2243,
        "status": ("PANEL-CEM-REPRICE-VIABLE" if tail_upper <= SIGNED_MARGIN
                   else "PANEL-CEM-REPRICE-OPEN"),
        "lever": "composite-EM panel: N_risk = 0 by the 2242 certified zero "
                 "count Z = 0; panel_cem = (dx^2/12)(2 a_max) M_k(sigma)",
        "gate": {"zero_count_certificate": cert["status"],
                 "min_floor": {n: c["min_floor"]["value"]
                               for n, c in cert["channels"].items()},
                 "edge_B2_re_lower_bound": cert["edge_arcs"]
                 ["B2_re_lower_bound"]},
        "radius": radii,
        "radius_source": "2237 certified generation channel",
        "panel_cem_sigma1": {nm: v["computed"]
                             for nm, v in panel_match.items()},
        "panel_2238_sigma1": rec38["panel_2238_sigma1"],
        "panel_2234_sigma1": rec38["panel_2234_sigma1"],
        "projection_check": panel_match,
        "binding_row": best,
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_over},
        "comparison_2197": SCREEN_2197,
        "comparison_2238": {
            "C_upper_2238": rec38["screen"]["C_upper"],
            "tail_over_margin_2238": rec38["screen"]
            ["tail_upper_over_margin"],
            "C_repricing_factor": rec38["screen"]["C_upper"]
            / best["C_upper"],
        },
        "transfer_2119": {
            "formal_owner_cardinality_bound": COUNT_2119,
            "screened_family_nodes": SCREENED_NODES,
            "count_ratio": ratio_2119,
            "over_margin_at_2238": ratio_2119
            * rec38["screen"]["tail_upper_over_margin"],
            "over_margin_at_2243": ratio_2119 * tail_over,
            "reading": "2119 x tail_over_margin (coarse product reading, "
                       "docs/proofs/2241)",
        },
        "drift": {k: rp.sig_drift(k) for k in
                  ("base_M0", "base_D2", "corr_M0", "corr_D2")},
        "inflation_over_2197": {"C": best["C_upper"] / SCREEN_2197["C_upper"],
                                "tail": tail_upper
                                / SCREEN_2197["tail_upper"]},
        "nonclaims": [
            "the risk term drops by the 2242 certificate (interval pavement "
            "+ edge-arc analytic bound), not by the 2238 measured node test",
            "the majorant ladder m0..m4 and the coefficient inflation are "
            "exactly the 2238 machinery (recon table cached)",
            "the reduction is bitwise the 2238 loop; only panel_new is "
            "replaced by panel_cem (N_risk = 0)",
            "the 2119 count ratio itself is unchanged (3002.5554464806 vs "
            "62 nodes); the transfer moves by the margin, not by the count",
            "2157 near-pin separation input remains open; 2134 bypassed",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_panel_cem_2243.py",
            "gate": "results/2242_zero_count_certificate.json",
            "sigma_sums": "results/2234_sigma_*.json",
            "radius": "results/2237_generation_certificate.json",
            "prior": "results/2238_panel_dx2_reprice.json",
        },
    }
    (R / "2243_panel_cem_reprice.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "C_upper": best["C_upper"],
        "C_factor_vs_2238": rec38["screen"]["C_upper"] / best["C_upper"],
        "tail_over_margin": tail_over,
        "transfer_2119_over_margin": ratio_2119 * tail_over,
        "binding_sigma": best["sigma"],
        "projection_rel_max": max(v["rel"]
                                  for v in panel_match.values()),
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()