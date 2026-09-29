"""Record 2224: assemble the binding-node input and MPFR implementation prices.

The input/operation term is the parameterized 2217 IEEE forward-error price;
the library term is the certified 2223 MPFR directed-rounding price.  The
labels stay separate so a measured/parameterized term is not misreported as
an outward bound.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
old = json.loads((R / "2217_weighted_zero_ieee_radius.json").read_text())
new = json.loads((R / "2223_mpfr_exp_binding.json").read_text())
binding = old["binding"]
input_price = float(binding["total"])
implementation_price = float(new["charge"]["total"])
target = 6.2550323e-5
result = {
    "record": 2224,
    "status": "BINDING-NODE-PARAMETERIZED-INPUT-PLUS-MPFR",
    "scope": {"node_index": binding["node_index"], "families": 30,
              "full_quadrature": True},
    "prices": {
        "input_q_and_operation_parameterized_2217": input_price,
        "exp_sin_cos_mpfr_certified_2223": implementation_price,
        "assembled": input_price + implementation_price,
        "target": target,
        "assembled_over_target": (input_price + implementation_price) / target,
    },
    "interpretation": [
        "2217 input/operation term is a parameterized IEEE forward-error price, not an outward certificate",
        "2223 transcendental term is a directed-rounding MPFR certificate at node 2",
        "other nodes, finite accumulation, and owner transfer remain open",
    ],
    "provenance": {"input": "results/2217_weighted_zero_ieee_radius.json",
                   "implementation": "results/2223_mpfr_exp_binding.json"},
}
(R / "2224_binding_combined_budget.json").write_text(
    json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps(result["prices"], indent=2))
