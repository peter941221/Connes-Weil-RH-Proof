"""Assemble the 2374 node price with the booked coordinate and panel terms.

This is an interface ledger, not a producer certificate.  The Lean theorem
audits the finite-sum coordinate-charge bridge; the numerical node import and
directed accumulation remain explicitly marked as open.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> dict:
    refinement_path = ROOT / "results/2374_nodal_interval_refinement.json"
    summary_path = ROOT / "results/2374_same_owner_refinement_776611.json"
    price_path = ROOT / "results/2371_coordinate_panel_price.json"
    refinement = json.loads(refinement_path.read_text())
    summary = json.loads(summary_path.read_text())
    price = json.loads(price_path.read_text())

    old_nodes = price["nodes"]
    new_nodes = refinement["nodes"]
    mesh_ratio_sq = ((old_nodes - 1) / (new_nodes - 1)) ** 2
    delta_old = price["coordinate_max_float_gap"]
    delta_new = float(Fraction(refinement["coordinate_max_fraction_gap"]))
    delta_ratio = delta_new / delta_old
    directed = summary["directed_integrals"]

    rows = []
    for channel, value in zip(price["rows"], directed):
        coordinate_charge = channel["coordinate_charge"] * delta_ratio
        panel_remainder = channel["panel_remainder"] * mesh_ratio_sq
        rows.append(
            {
                "channel": channel["channel"],
                "actual_node_composite": value,
                "coordinate_charge": coordinate_charge,
                "ideal_node_composite_upper": value + coordinate_charge,
                "panel_remainder": panel_remainder,
                "assembled_upper": value + coordinate_charge + panel_remainder,
            }
        )

    result = {
        "record": 2375,
        "status": "COMPOSITE_COORDINATE_BRIDGE_INTERFACE_ONLY",
        "nodes": new_nodes,
        "old_price_nodes": old_nodes,
        "coordinate_delta": delta_new,
        "coordinate_delta_ratio_to_2371": delta_ratio,
        "panel_mesh_ratio_squared_to_2371": mesh_ratio_sq,
        "rows": rows,
        "lean_bridge_theorem": "compositeNodeUpper_le_of_nodewise_coordinate_charge2359",
        "lean_bridge_audited": True,
        "nodewise_numeric_import_proved": False,
        "directed_accumulation_theorem_proved": refinement["directed_accumulation_theorem_proved"],
        "trapezoid_remainder_proved": refinement["trapezoid_remainder_proved"],
        "producer_go": False,
        "rh_claim": False,
        "input_hashes": {
            "refinement": hashlib.sha256(refinement_path.read_bytes()).hexdigest(),
            "summary": hashlib.sha256(summary_path.read_bytes()).hexdigest(),
            "price": hashlib.sha256(price_path.read_bytes()).hexdigest(),
        },
    }
    output = ROOT / "results/2375_composite_charge_bridge.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "rows": rows}, indent=2))
    return result


if __name__ == "__main__":
    main()
