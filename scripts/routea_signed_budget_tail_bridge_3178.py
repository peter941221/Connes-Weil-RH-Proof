"""Bridge tail acceptance evidence without promoting it to a gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read_json(relative: str):
    path = ROOT / relative
    raw = path.read_bytes()
    return json.loads(raw.decode("utf-8")), hashlib.sha256(raw).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/3178_routea_signed_budget_tail_bridge.json")
    args = parser.parse_args()
    tail, tail_hash = read_json("results/2353_same_owner_tail_supplier.json")
    acceptance, acceptance_hash = read_json("results/2354_same_owner_tail_acceptance.json")
    legacy, legacy_hash = read_json("results/2038_route_a_one_copy_interval_certificate_audit.json")

    lanes = []
    for row in acceptance["positive_lambda_lanes"]:
        ratio = Fraction(row["ratio_exact"])
        lanes.append({
            "iterate": row["iterate"],
            "shell": row["shell"],
            "lambda_exact": row["lambda_exact"],
            "ratio_exact": row["ratio_exact"],
            "headroom_exact": str(1 - ratio),
            "headroom_display": float(1 - ratio),
            "registered_scalar_budget_pass": row["registered_scalar_budget_pass"],
            "not_a_gate_row": row["not_a_gate_row"],
            "actual_tail_acceptance_instantiated": row["actual_tail_acceptance_instantiated"],
        })

    components = legacy["certificate_components"]
    result = {
        "record": 3178,
        "status": "TAIL_BRIDGED_MAIN_BUDGET_STILL_OPEN",
        "tail_supplier": {
            "threshold_exact": tail["certified_base_threshold_exact"],
            "q_exact": tail["certified_base_q_exact"],
            "both_height_signs": "both signs and all abs(t)>=T" in tail["supplier_scope"],
            "base_order4_exact": tail["whole_line_angular_constants_exact"]["base_order4"],
            "correction_order2_exact": tail["whole_line_angular_constants_exact"]["correction_order2"],
            "full_signed_kernel_priced": tail["full_signed_kernel_priced"],
            "tail_supplier_imported_in_lean": tail["tail_supplier_imported_in_lean"],
        },
        "scalar_acceptance_lanes": lanes,
        "main_budget": {
            "missing_certificate_components": [name for name, state in components.items() if state != "CLOSED"],
            "finite_window_interval": components["finite_window_quadrature_error"],
            "full_line_tail": components["full_line_tail_bound"],
            "negative_aggregate_margin_closed": False,
        },
        "semantic_boundary": {
            "scalar_lane_can_be_added_to_physical_kernel_budget": False,
            "reason": "2354 marks each row not_a_gate_row; its ratio is a conditional scalar acceptance inequality, not a signed prime-node aggregate bound",
            "owner_transfer_closed": False,
        },
        "input_sha256": {
            "results/2353_same_owner_tail_supplier.json": tail_hash,
            "results/2354_same_owner_tail_acceptance.json": acceptance_hash,
            "results/2038_route_a_one_copy_interval_certificate_audit.json": legacy_hash,
        },
        "producer_go": False,
        "rh_claim": False,
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
