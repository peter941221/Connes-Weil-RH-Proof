"""Record 2239: x-channel charge over all 30 owner nodes.

Record 2233 priced the x-channel (one and sixteen ulps of the stored
binary64 x node, charged through the dimensionless derivative bounds
d1 = 2K|x|/a^2 (1-u^2)^-2 + |z| and d2 = (2K/a^2)((1-u^2)^-2 +
4u^2 (1-u^2)^-3), re-evaluated at nextafter-up(rr + ri + extra_k)) for
the two sampled nodes 2 (binding charge) and 1 (minimum charge).  This
record extends the same sweep to all 30 owner nodes: 900 chunk files
2233x_node<i>_fam<f>_<g>.json, each carrying one family's rows
(gl_base/k1/k16, sim_base/k1/k16, max_delta_base/k1/k16).

Aggregation is bitwise-identical to 2233's reduce (families sorted, one
nextafter-up per (gl + sim) addition) and the nodes 2/1 rows are
asserted equal to the committed 2233 artifact entry for entry.  The base
column is a drift control against the committed 2229 exp_lipschitz_charge
of the same node.

Mode (environment):
  MODE=reduce  -> results/2239_xwidth_charge_all_nodes.json
"""
import json
import math
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
TARGET_2224 = 6.2550323e-05


def up(v):
    return math.nextafter(v, math.inf)


def reduce_all():
    per_node = {}
    for ni in range(30):
        rows = []
        for path in sorted(R.glob(f"2233x_node{ni}_fam*.json")):
            rows.extend(json.loads(path.read_text(encoding="utf-8"))["rows"])
        rows.sort(key=lambda r: r["family"])
        assert len(rows) == 30, (ni, len(rows))
        assert [r["family"] for r in rows] == list(range(30)), ni
        totals = {}
        for tag in ("base", "k1", "k16"):
            t = 0.0
            for r in rows:
                t = up(t + r[f"gl_{tag}"] + r[f"sim_{tag}"])
            totals[tag] = t
        cpath = R / f"2229_q_mpfr_node{ni}.json"
        assert cpath.exists(), ni
        committed = json.loads(cpath.read_text(encoding="utf-8"))[
            "exp_lipschitz_charge"]
        max_delta = {tag: max(r[f"max_delta_{tag}"] for r in rows)
                     for tag in ("base", "k1", "k16")}
        per_node[str(ni)] = {
            "totals": totals,
            "committed_2229": committed,
            "base_relative_drift": (totals["base"] - committed) / committed,
            "delta_charge_k1": totals["k1"] - totals["base"],
            "delta_charge_k16": totals["k16"] - totals["base"],
            "inflation_k1": totals["k1"] / totals["base"] - 1.0,
            "inflation_k16": totals["k16"] / totals["base"] - 1.0,
            "max_delta": max_delta,
        }
    gate = {}
    c33 = json.loads((R / "2233_xwidth_charge.json")
                     .read_text(encoding="utf-8"))
    for ni, b in c33["per_node"].items():
        a = per_node[ni]
        same = (a["totals"] == b["totals"]
                and a["inflation_k1"] == b["inflation_k1"]
                and a["inflation_k16"] == b["inflation_k16"]
                and a["max_delta"] == b["max_delta"])
        gate[ni] = same
        assert same, ("2233 two-node reproduction", ni)
    worst1 = max(per_node, key=lambda i: per_node[i]["inflation_k1"])
    worst16 = max(per_node, key=lambda i: per_node[i]["inflation_k16"])
    drift_max = max(abs(v["base_relative_drift"]) for v in per_node.values())
    # one-ulp absolute charge at the worst node, as a fraction of the
    # 2224 target: each node's q ledger charges the x channel through
    # |dq/dx| d_1, which is exactly delta_charge_k1 of this sweep.
    frac1 = per_node[worst1]["delta_charge_k1"] / TARGET_2224
    result = {
        "record": 2239,
        "part": "x-channel-all-nodes",
        "status": "XWIDTH-CHARGE-ALL-NODES-MEASURED",
        "model": {
            "delta_k": "k * 2^-52 * |x|, one and sixteen ulps of the stored "
                       "binary64 x node",
            "shift": "|dq| <= |dq/dx| d_k + (1/2)|q''| d_k^2 with analytic "
                     "d1 = 2K|x|/a^2 (1-u^2)^-2 + |z|, "
                     "d2 = (2K/a^2)((1-u^2)^-2 + 4u^2 (1-u^2)^-3)",
            "charge": "re-evaluated at nextafter-up(rr + ri + extra) with "
                      "MPFR RNDU accumulation",
        },
        "per_node": per_node,
        "worst_node_k1": int(worst1),
        "worst_node_k16": int(worst16),
        "worst_inflation_k1": per_node[worst1]["inflation_k1"],
        "worst_inflation_k16": per_node[worst16]["inflation_k16"],
        "worst_one_ulp_charge": per_node[worst1]["delta_charge_k1"],
        "worst_one_ulp_over_target": frac1,
        "base_drift_abs_max": drift_max,
        "node2_1_bitwise_vs_2233": gate,
        "budget_reading": {
            "target_2224": TARGET_2224,
            "reading": "worst-node one-ulp absolute charge over the 2224 "
                       "target; the x channel enters each node's q ledger "
                       "as |dq/dx| d_1",
        },
        "nonclaims": [
            "the GL/Simpson nodes are taken from the stored binary64 grids; "
            "k ulps is a stated model of their generation error, not a "
            "certified bound on it",
            "the sweep is per node; the ledger uses the binding node's row",
            "convention A (stored operands exact) remains the certificate "
            "reference",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_xwidth_charge_all_nodes_2239.py",
            "chunks": "results/2233x_node*_fam*.json (900 files)",
            "charge_backend": "scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py",
            "reproduced": "results/2233_xwidth_charge.json (nodes 2/1)",
        },
    }
    out = R / "2239_xwidth_charge_all_nodes.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "worst_node_k1": int(worst1),
                      "worst_inflation_k1": per_node[worst1]["inflation_k1"],
                      "worst_node_k16": int(worst16),
                      "worst_inflation_k16": per_node[worst16]["inflation_k16"],
                      "worst_one_ulp_over_target": frac1,
                      "base_drift_abs_max": drift_max,
                      "gate": gate}, indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "reduce")
    if mode == "reduce":
        reduce_all()
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()