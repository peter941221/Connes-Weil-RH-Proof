"""Current-source audit for the repaired full-grid numerical interface.

This checks the replay's same-expression controls and its bridge readback.  It
does not prove the mathematical pointwise enclosure or import numbers into
Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2422_repaired_shared_geometry_776611.json"
BRIDGE = ROOT / "results/2424_repaired_span_composite_bridge.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(artifact_path: Path = ARTIFACT, bridge_path: Path = BRIDGE,
         output_path: Path | None = None, record: int = 2426) -> dict:
    artifact = json.loads(artifact_path.read_text())
    bridge = json.loads(bridge_path.read_text())
    source = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    require(artifact["source_sha256"] == sha256(source), "worker hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator),
            "evaluator hash mismatch")
    require(artifact["nodes"] == 776611 and artifact["span"] == 20001,
            "unexpected replay dimensions")
    require(artifact["workers"] == 16, "unexpected worker count")
    require(artifact["exact_binary64_audit_enabled"], "exact audit disabled")
    for key in (
        "directed_span_dominates_exact_binary64_sum",
        "directed_integral_dominates_exact_binary64_integral",
        "directed_term_binary64_roundup_dominates_mpfr",
        "mpfr_span_dominates_exact_binary64_sum",
    ):
        require(artifact[key] == [True, True, True, True], f"{key} failed")
    rows = artifact["directed_term_binary64_roundup_span_integrals"]
    require(len(rows) == 39, "expected 39 span rows")
    lengths = [min((i + 1) * artifact["span"], artifact["nodes"])
               - i * artifact["span"] for i in range(len(rows))]
    require(lengths == [20001] * 38 + [16573], "span partition mismatch")
    require(all(math.isfinite(value) and value >= 0
                 for row in rows for value in row), "invalid span witness")
    current_parent = artifact["directed_term_binary64_roundup_integrals"]
    require(len(bridge["rows"]) == 4, "bridge channel width mismatch")
    for channel, row in enumerate(bridge["rows"]):
        span_sum = sum(part[channel] for part in rows)
        require(row["span_sum_node_composite"] == span_sum,
                f"bridge span sum mismatch at channel {channel}")
        require(row["parent_roundup_node_composite"] == current_parent[channel],
                f"bridge parent mismatch at channel {channel}")
        require(row["assembled_upper"] ==
                row["ideal_node_composite_upper"] + row["panel_remainder"],
                f"bridge assembly mismatch at channel {channel}")
    result = {
        "record": record,
        "status": "CURRENT_FULLGRID_INTERFACE_AUDIT_PASS",
        "artifact": str(artifact_path.relative_to(ROOT)),
        "bridge": str(bridge_path.relative_to(ROOT)),
        "source_hashes_match": True,
        "nodes": artifact["nodes"],
        "span": artifact["span"],
        "span_count": len(rows),
        "same_expression_controls_pass": True,
        "current_parent_and_span_bridge_match": True,
        "pointwise_mathematical_term_dominance_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = output_path or (ROOT / f"results/{record}_current_fullgrid_audit.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--bridge", type=Path, default=BRIDGE)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--record", type=int, default=2426)
    args = parser.parse_args()
    artifact = args.artifact if args.artifact.is_absolute() else ROOT / args.artifact
    bridge = args.bridge if args.bridge.is_absolute() else ROOT / args.bridge
    output = args.output if args.output is None or args.output.is_absolute() else ROOT / args.output
    main(artifact, bridge, output, args.record)
