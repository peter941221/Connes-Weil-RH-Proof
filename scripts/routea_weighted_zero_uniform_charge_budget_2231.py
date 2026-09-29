"""Record 2231: uniform charge vs candidate budget.

Reads the 2229 all-node outward envelope (`2229_q_mpfr_all_nodes.json`) and
prices the single uniform charge

    m = max_node exp_lipschitz_charge

against the candidate budget chain already on the shelf:

    2211/2217 combined-correction target       6.2550323e-05   (absolute)
    2217 parameterized AMP price (binding node) 2.459424789942387e-08
    2223 MPFR implementation price              7.039855400051501e-12
    2197 signed-margin anchor                   1.675397327895099e12

The outward 2229 charge replaces the 2217 parameterized term in the 2224
assembly; the replayed assembly is `m + 2223` and its ratio to the target is
the uniform-charge budget reading.  Drift control: the 2229 envelope readings
at nodes 2, 3, 29 against the 2228 in-process readings.

Status is UNIFORM-CHARGE-PRICED only when all 30 nodes are present with zero
interval failures; otherwise UNIFORM-CHARGE-INCOMPLETE.  No RH claim.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"

TARGET = 6.2550323e-05
ANCHOR = 1.675397327895099e12
NODE_COUNT = 30
DRIFT_NODES = (2, 3, 29)


def _load(name):
    return json.loads((R / name).read_text(encoding="utf-8"))


def main():
    summary = _load("2229_q_mpfr_all_nodes.json")
    charges = {int(k): v for k, v in summary["charges"].items()}
    missing = [i for i in range(NODE_COUNT) if i not in charges]
    failures = summary.get("total_failures")
    present = len(charges) == NODE_COUNT and not missing

    worst = max(charges, key=lambda i: charges[i])
    uniform = charges[worst]

    amp = _load("2217_weighted_zero_ieee_radius.json")
    impl = _load("2223_mpfr_exp_binding.json")
    amp_price = amp["binding"]["total"]
    impl_price = impl["charge"]["total"]
    assembled = uniform + impl_price

    drift = {}
    for ni in DRIFT_NODES:
        p = R / f"2228_q_mpfr_node{ni}.json"
        if not p.exists() or ni not in charges:
            continue
        old = json.loads(p.read_text(encoding="utf-8"))["exp_lipschitz_charge"]
        drift[ni] = {"2228": old, "2229": charges[ni],
                     "relative_increase": charges[ni] / old - 1.0}

    result = {
        "record": 2231,
        "status": ("UNIFORM-CHARGE-PRICED" if present and not failures
                   else "UNIFORM-CHARGE-INCOMPLETE"),
        "scope": {"nodes_present": len(charges), "missing": missing,
                  "nodes_expected": NODE_COUNT,
                  "interval_failures": failures,
                  "source": "results/2229_q_mpfr_all_nodes.json",
                  "operand_cache_md5": summary.get("operand_cache", {}).get("md5")},
        "uniform_charge": {"value": uniform, "worst_node": worst,
                           "min_node_charge": min(charges.values()),
                           "max_over_min": uniform / min(charges.values())},
        "budget": {
            "target_2211_2217": TARGET,
            "uniform_over_target": uniform / TARGET,
            "impl_2223": impl_price,
            "assembled_replay": assembled,
            "assembled_over_target": assembled / TARGET,
            "amp_2217_price": amp_price,
            "amp_over_uniform": amp_price / uniform,
            "anchor_2197": ANCHOR,
            "uniform_over_anchor": uniform / ANCHOR,
        },
        "drift_2228_to_2229": drift,
        "nonclaims": [
            "binary64 operands are taken as exact (discrete-defined "
            "convention; record 2230)",
            "uniform charge is the exponent-radius charge only; the operand "
            "construction ledger (coefficient solve, quadrature generation "
            "error), the low-shell/B_zm side, complete-owner transfer, and "
            "the strict signed margin remain open",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_uniform_charge_budget_2231.py",
            "inputs": ["results/2229_q_mpfr_all_nodes.json",
                       "results/2217_weighted_zero_ieee_radius.json",
                       "results/2223_mpfr_exp_binding.json",
                       "results/2228_q_mpfr_node{2,3,29}.json"],
        },
    }
    out = R / "2231_uniform_charge_vs_budget.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()