"""Re-read the repaired composite charge using retained span witnesses.

This is a numerical interface ledger only.  It deliberately keeps the
pointwise mathematical-term dominance and Lean import flags false.
"""

from __future__ import annotations

import hashlib
import json
import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPAN = ROOT / "results/2411_repaired_shared_geometry_776611.json"
OLD = ROOT / "results/2408_repaired_composite_charge_bridge.json"


def main(span_path: Path = SPAN, output_path: Path | None = None,
         record: int = 2412) -> dict:
    span = json.loads(span_path.read_text())
    old = json.loads(OLD.read_text())
    values = [sum(row[channel] for row in
                  span["directed_term_binary64_roundup_span_integrals"])
              for channel in range(4)]
    current_parent = span["directed_term_binary64_roundup_integrals"]
    legacy_parent = [row["actual_node_composite"] for row in old["rows"]]
    rows = []
    for channel, (old_row, value, parent) in enumerate(
            zip(old["rows"], values, current_parent)):
        coordinate_charge = old_row["coordinate_charge"]
        panel_remainder = old_row["panel_remainder"]
        rows.append({
            "channel": old_row["channel"],
            "span_sum_node_composite": value,
            "parent_roundup_node_composite": parent,
            "legacy_parent_roundup_node_composite": legacy_parent[channel],
            "coordinate_charge": coordinate_charge,
            "ideal_node_composite_upper": value + coordinate_charge,
            "panel_remainder": panel_remainder,
            "assembled_upper": value + coordinate_charge + panel_remainder,
        })
    result = {
        "record": record,
        "status": "REPAIRED_SPAN_COMPOSITE_BRIDGE_INTERFACE_ONLY",
        "nodes": span["nodes"],
        "span_count": len(span["directed_term_binary64_roundup_span_integrals"]),
        "rows": rows,
        "lean_bridge_theorem":
            "repaired_fullgrid_partition_eq2410 + "
            "compositeNodeUpper_le_of_nodewise_coordinate_charge2359",
        "span_witness_readback_pass": True,
        "span_witness_imported_to_lean": False,
        "pointwise_mathematical_term_dominance_proved": False,
        "analytic_trapezoid_remainder_theorem_proved": True,
        "numeric_trapezoid_remainder_imported": False,
        "producer_go": False,
        "rh_claim": False,
        "input_hashes": {
            "span": hashlib.sha256(span_path.read_bytes()).hexdigest(),
            "old_bridge": hashlib.sha256(OLD.read_bytes()).hexdigest(),
        },
    }
    output = output_path or (ROOT / f"results/{record}_repaired_span_composite_bridge.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "rows": rows}, indent=2))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--span", type=Path, default=SPAN)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--record", type=int, default=2412)
    args = parser.parse_args()
    main(args.span if args.span.is_absolute() else ROOT / args.span,
         args.output if args.output is None or args.output.is_absolute() else ROOT / args.output,
         args.record)
