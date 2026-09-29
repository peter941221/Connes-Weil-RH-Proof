#!/usr/bin/env python3
"""2253 - Per-node charge split of the direct-product screen (L2 charge side).

Consumer: the CHARGE side of the 2246 L2 transfer, registered open by 2250
as "per-node charge <= uniform per-node budget tail/62".  This record
measures the only canonical per-node split available from the committed
machinery - the absolute-value (triangle) decomposition of the
direct-product mass screen over the 30 construction nodes at the binding
sigma=1 row (2234/2238/2243) - and prices the consequence.

Result (registered): the uniform per-node budget is FALSIFIED by
measurement.  The split total exceeds the screen and single nodes exceed
the budget by two orders of magnitude; the count-side reduction factor
(owner/62) of the 2246 ledger is therefore WITHDRAWN, and the count-free
Lean fallback (charge = the full high-shell tail, supported by
`exists_weightedZeroMeasure_highShell_tsum_bound` with B = the mass-screen
constant) keeps the item-5 strict signed margin with eps0 > 0 against the
2249 certified margin.  Screening artifact: no producer GO, no gate sign
change, no RH claim.

Per-node charge (channel a, the binding channel):
    q_j  = outward bound of  int e^{x} |beta_j| |f_j''(x)| dx
           on the committed 2197/2234 grid, sigma = 1
    P    = the 2243 corr_M0 inflated row bound at sigma = 1
    T_j  = 4 * mult_2248 * q_j * P      (ledger units)
Sampling: trapezoid on NX=240001 nodes; per-node panel charge from the
2234 Lipschitz majorants (|f''| + |f'''| form), per-node solve-radius
share e2_j exactly as 2234 sums it, sigma cover exp(a_max * 0.01), and a
2^-45 relative float slack on the measured sums.  Writes
results/2253_pernode_charge_uniformity.json.
"""
import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_direct_product_outward_2234 as o34  # noqa: E402
import routea_weighted_zero_direct_product_mass_screen_2197 as s97  # noqa: E402
import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402

import mpmath as mp  # noqa: E402

RECORD = 2253
ARTIFACT_2243 = ROOT / "results" / "2243_panel_cem_reprice.json"
ARTIFACT_2237 = ROOT / "results" / "2237_generation_certificate.json"
OUTPUT = ROOT / "results" / "2253_pernode_charge_uniformity.json"

# ledger constants (2248 standing / 2249 certified margin)
TAIL_2248 = 4894093747.764274
MULT_2248 = 128.70692502980964
KNOWN_ERROR_2109 = 74601530.30234718
MARGIN_LO_2249 = 1675396046388.2737
SCREEN_NODES = 62.0
FLOAT_SLACK_EXP = 45
D_SIGMA = 0.01


def fsum(values):
    return math.fsum(float(v) for v in values)


def main():
    screen = json.loads(ARTIFACT_2243.read_text(encoding="utf-8"))
    cert37 = json.loads(ARTIFACT_2237.read_text(encoding="utf-8"))
    row = screen["binding_row"]
    assert row["sigma"] == 1.0
    db = row["base_D2"]
    mc = row["corr_M0"]
    mb = row["base_M0"]
    eb2 = row["coeff_infl_base_D2"]
    r_base = cert37["radius"]["r_base"]

    fam, base, corr, a_max = o34.build_construction()
    nfam = len(fam)
    assert nfam == 30
    cover1 = math.exp(a_max * D_SIGMA)

    # node labels: same construction calls as 2249.build()
    rho = (0.5 + s97.DELTA) + 1j * s97.GAMMA
    nodes, values = r94.owner_nodes_ext(rho, s97.GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(
                abs(z - e) > 1e-6 for e in nodes):
            nodes.append(z)
            values.append(0j)
    assert len(nodes) == 30
    labels = []
    for z, v in zip(nodes, values):
        if v != 0:
            kind = "target"
        elif abs(z.imag) <= 1e-9:
            kind = "real_pin"
        elif abs(z.real - 0.5) > 1e-9:
            kind = "offline_pin"
        else:
            zval = float(abs(mp.siegelz(mp.mpf(z.imag))))
            kind = "zero" if zval < 1e-9 else "kills_pin"
        labels.append(kind)
    assert labels.count("zero") == 21, labels
    assert labels.count("target") == 3
    assert labels.count("offline_pin") == 2
    assert labels.count("real_pin") == 3
    assert labels.count("kills_pin") == 1

    # committed grid of the 2234 machinery
    NX = s97.NX
    x = np.linspace(-a_max, a_max, NX)
    dx = (2.0 * a_max) / (NX - 1)
    tw = np.full(NX, 2.0)
    tw[0] = tw[-1] = 1.0
    wgt = (dx / 2.0) * tw
    ex = np.exp(x)
    K = s97.K

    def majorant3(th):
        # per-node Lipschitz majorant combination for e^x f'': |f''| + |f'''|
        def comb(a, w):
            c0 = o34.majorant_phi_le(0, K, a)
            c1 = o34.majorant_phi_le(1, K, a)
            c2 = o34.majorant_phi_le(2, K, a)
            c3 = o34.majorant_phi_le(3, K, a)
            m2 = c2 + 2.0 * abs(th) * c1 + th * th * c0
            m3 = c3 + 3.0 * abs(th) * c2 + 3.0 * th * th * c1 \
                + abs(th) ** 3 * c0
            return w * (m2 + m3)

        def comb0(a, w):
            c0 = o34.majorant_phi_le(0, K, a)
            c1 = o34.majorant_phi_le(1, K, a)
            return w * (c1 + abs(th) * c0 + c0)
        return comb, comb0

    mass = {"base_d2": np.zeros(nfam), "base_m0": np.zeros(nfam),
            "corr_d2": np.zeros(nfam), "corr_m0": np.zeros(nfam)}
    panel = {"base_d2": np.zeros(nfam), "base_m0": np.zeros(nfam),
             "corr_d2": np.zeros(nfam), "corr_m0": np.zeros(nfam)}
    slack = {"base_d2": np.zeros(nfam), "base_m0": np.zeros(nfam),
             "corr_d2": np.zeros(nfam), "corr_m0": np.zeros(nfam)}
    infl = {"base": np.zeros(nfam), "corr": np.zeros(nfam)}
    for j, (a, th) in enumerate(fam):
        comb, comb0 = majorant3(th)
        u = x / a
        qv = 1.0 - u * u
        mask = qv > 0.0
        phi = np.zeros(NX)
        phi[mask] = np.exp(-K / qv[mask])
        e1 = np.zeros(NX)
        e2 = np.zeros(NX)
        e1[mask] = -2.0 * K * u[mask] / (a * qv[mask] ** 2)
        e2[mask] = (-2.0 * K / (a * a)
                    * (1.0 / qv[mask] ** 2
                       + 4.0 * u[mask] ** 2 / qv[mask] ** 3))
        g = e2 + e1 * e1 - th * th
        h = 2.0 * th * e1
        d2 = np.hypot(g, h) * phi
        for name, coef, integ in (("base_d2", base, d2),
                                  ("base_m0", base, phi),
                                  ("corr_d2", corr, d2),
                                  ("corr_m0", corr, phi)):
            terms = wgt * ex * integ * abs(coef[j])
            mass[name][j] = fsum(terms)
            slack[name][j] = (2.0 ** -FLOAT_SLACK_EXP) * fsum(np.abs(terms))
        panel["base_d2"][j] = comb(a, abs(base[j])) \
            * (2.0 * a_max) * dx / 4.0 * math.exp(a_max)
        panel["base_m0"][j] = comb0(a, abs(base[j])) \
            * (2.0 * a_max) * dx / 4.0 * math.exp(a_max)
        panel["corr_d2"][j] = comb(a, abs(corr[j])) \
            * (2.0 * a_max) * dx / 4.0 * math.exp(a_max)
        panel["corr_m0"][j] = comb0(a, abs(corr[j])) \
            * (2.0 * a_max) * dx / 4.0 * math.exp(a_max)
        e2j_b = r_base * 2.0 * a * math.exp(a_max) \
            * o34.majorant_phi_le(2, K, a)
        e2j_c = cert37["radius"]["r_corr"] * 2.0 * a * math.exp(a_max) \
            * o34.majorant_phi_le(2, K, a)
        infl["base"][j] = e2j_b
        infl["corr"][j] = e2j_c

    # outward per-node masses: (I + panel) * (1 + e2_j) * cover1 + slack
    def q_out(name, side):
        return ((mass[name] + panel[name]) * (1.0 + infl[side]) * cover1
                + slack[name])

    bd2 = q_out("base_d2", "base")
    cd2 = q_out("corr_d2", "corr")

    # cross-check: the per-node panel sums reproduce the 2234-style
    # aggregate trapezoid panel and the aggregate solve inflation
    _, L_b2 = o34.integrand_lipschitz(base, fam, K, a_max, 1.0)
    panel_checks = {
        "panel_base_D2_2234_aggregate": L_b2 * (2.0 * a_max) * dx / 4.0,
        "panel_base_D2_pernode_sum": float(panel["base_d2"].sum()),
        "panel_base_D2_cem_artifact": row["panel_base_D2"],
        "coeff_infl_base_D2_artifact": eb2,
        "coeff_infl_base_D2_pernode_sum": float(infl["base"].sum()),
    }

    budget_mass = (math.pi * 2.0) ** 2 * screen["screen"]["C_upper"] / SCREEN_NODES
    # channel a (binding): per-node charge = 4 mult q_j P ; channel b analog
    ta = 4.0 * MULT_2248 * bd2 * mc           # channel a per-node charges
    tb = 4.0 * MULT_2248 * cd2 * mb           # channel b per-node charges
    budget = TAIL_2248 / SCREEN_NODES
    ta_max = int(np.argmax(ta))
    tb_max = int(np.argmax(tb))
    zero_idx = [j for j in range(nfam) if labels[j] == "zero"]
    ta_zmax = max(zero_idx, key=lambda j: ta[j])

    split_total_a = float(ta.sum())
    split_total_b = float(tb.sum())
    sum_zero_a = float(ta[zero_idx].sum())
    sum_nonzero_a = float(ta.sum() - ta[zero_idx].sum())

    # full-tail fallback ledger (count-free Lean bound)
    charge_full = TAIL_2248 + KNOWN_ERROR_2109
    reading_full = charge_full / MARGIN_LO_2249
    eps0_full = MARGIN_LO_2249 - charge_full

    # withdrawn transfer ledger (kept for the record)
    transfer = {}
    for key, ratio in (("unconditional", 26.0 / 62.0),
                       ("imported", 21.0 / 62.0)):
        charge = TAIL_2248 * ratio + KNOWN_ERROR_2109
        transfer[key] = {"ratio": ratio, "charge": charge,
                         "reading_vs_2249_margin": charge / MARGIN_LO_2249,
                         "eps0": MARGIN_LO_2249 - charge,
                         "status": "WITHDRAWN (per-node budget falsified)"}

    rows = []
    for j in range(nfam):
        rows.append({
            "index": j, "kind": labels[j],
            "node": [nodes[j].real, nodes[j].imag],
            "a": fam[j][0], "theta": fam[j][1],
            "abs_base": float(abs(base[j])), "abs_corr": float(abs(corr[j])),
            "base_d2_mass_outward": float(bd2[j]),
            "corr_d2_mass_outward": float(cd2[j]),
            "charge_channel_a": float(ta[j]),
            "charge_channel_b": float(tb[j]),
            "ratio_over_budget_a": float(ta[j] / budget),
            "ratio_over_budget_b": float(tb[j] / budget),
        })
    rows_sorted = sorted(rows, key=lambda r: -r["charge_channel_a"])

    result = {
        "record": RECORD,
        "status": "PER-NODE-CHARGE-BUDGET-FALSIFIED + FULL-TAIL-FALLBACK-VIABLE",
        "date": "2026-09-30",
        "candidate": {"rho": [0.945, s97.GAMMA], "delta": s97.DELTA,
                      "scale": s97.SCALE, "a_max": a_max},
        "screen": {"C_upper": screen["screen"]["C_upper"],
                   "B_upper_2243": screen["screen"]["B_upper"],
                   "tail_2248": TAIL_2248, "mult_2248": MULT_2248,
                   "screen_nodes": SCREEN_NODES,
                   "per_node_budget_ledger": budget,
                   "per_node_budget_mass": budget_mass},
        "per_node_charges": {
            "rows": rows,
            "max_channel_a": rows_sorted[0],
            "max_channel_a_over_zeros": next(
                r for r in rows_sorted if r["kind"] == "zero"),
            "max_channel_b_node": int(tb_max),
            "max_channel_b": float(tb.max()),
            "split_total_channel_a": split_total_a,
            "split_total_channel_b": split_total_b,
            "split_total_a_over_tail": split_total_a / TAIL_2248,
            "split_total_b_over_tail": split_total_b / TAIL_2248,
            "zeros_total_channel_a": sum_zero_a,
            "nonzero_total_channel_a": sum_nonzero_a,
            "zeros_total_over_tail": sum_zero_a / TAIL_2248,
        },
        "screen_decomposition_check": {
            "per_node_split_over_artifact_a": {
                "bd2_sum": float(bd2.sum()), "artifact_base_D2": db,
                "ratio": float(bd2.sum()) / db},
            "corr_partner_bound_mc": mc,
            "base_partner_bound_mb": mb,
            "panel_checks": panel_checks,
        },
        "falsification": {
            "claim": "per-node charge <= tail/62 (2246 L2 charge side)",
            "max_ratio_channel_a_all": float(ta.max() / budget),
            "max_ratio_channel_a_zeros": float(ta[ta_zmax] / budget),
            "argmax_all": {"index": ta_max, "kind": labels[ta_max]},
            "argmax_zeros": {"index": ta_zmax, "kind": labels[ta_zmax]},
            "verdict": "falsified at the committed absolute-value split; "
                       "the count-side transfer factor is withdrawn",
        },
        "fallback_ledger_full_tail": {
            "charge": charge_full, "reading_vs_2249_margin": reading_full,
            "eps0": eps0_full,
            "hypothesis": ("Lean exists_weightedZeroMeasure_highShell_"
                           "tsum_bound instantiated at the constructed F "
                           "with B = the mass-screen constant: the tail "
                           "bounds the owner tsum with no count factor; "
                           "the (owner/62) shave was an optional "
                           "count-side reduction"),
        },
        "withdrawn_transfer_ledger": transfer,
        "nonclaims": [
            "the per-node split is the absolute-value (triangle) "
            "decomposition; a cancellation-aware per-node split is not "
            "constructed here and remains the missing mechanism for any "
            "count-side reduction",
            "the fallback charges the full Lean tail; its formal assembly "
            "with the numeric B_upper is the registered remaining step "
            "(the 2252 Lean brick carries the arithmetic downstream)",
            "the outward accounting is first-order-shadow grade (float64 "
            "sums, 2^-45 slack, 2234 majorants), not MPFR per-node "
            "arithmetic; margins are two orders of magnitude wide",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_pernode_charge_2253.py",
            "inputs": ["results/2243_panel_cem_reprice.json",
                       "results/2237_generation_certificate.json",
                       "results/2234_build_cache.npz",
                       "scripts/routea_weighted_zero_direct_product_outward_2234.py"],
            "recon": "scripts/routea_weighted_zero_pernode_charge_recon_2253.py",
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    brief = {
        "status": result["status"],
        "max_ratio_all": result["falsification"]["max_ratio_channel_a_all"],
        "max_ratio_zeros":
            result["falsification"]["max_ratio_channel_a_zeros"],
        "split_total_a_over_tail":
            result["per_node_charges"]["split_total_a_over_tail"],
        "fallback": result["fallback_ledger_full_tail"],
    }
    print(json.dumps(brief, indent=2))


if __name__ == "__main__":
    main()