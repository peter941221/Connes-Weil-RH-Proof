"""Independent readback for the repaired 2406 full-grid replay.

This checks source hashes, the ordered partition dimensions, and the
same-expression binary64 directed controls.  It deliberately does not reuse
the superseded 2386 bridge, whose node totals were produced by the previous
evaluator revision.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2406_repaired_shared_geometry_776611.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> dict:
    artifact = json.loads(ARTIFACT.read_text())
    bridge = json.loads(
        (ROOT / "results/2408_repaired_composite_charge_bridge.json").read_text())
    source = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    require(artifact["source_sha256"] == sha256(source),
            "2359 source hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator),
            "2242 evaluator source hash mismatch")
    require(artifact["nodes"] == 776611 and artifact["span"] == 20001,
            "unexpected full-grid dimensions")
    require(artifact["workers"] == 16, "unexpected worker count")
    require(artifact["exact_binary64_audit_enabled"],
            "exact binary64 audit is disabled")
    require(artifact["directed_span_dominates_exact_binary64_sum"] ==
            [True, True, True, True],
            "same-expression span dominance failed")
    require(artifact["directed_integral_dominates_exact_binary64_integral"] ==
            [True, True, True, True],
            "same-expression integral dominance failed")
    require(artifact["directed_term_binary64_roundup_dominates_mpfr"] ==
            [True, True, True, True],
            "term roundup dominance failed")
    require(all(math.isfinite(value) and value >= 0
                 for value in artifact["interval_integrals"]),
            "non-finite or negative interval integral")
    require(artifact["interval_min_product"] > 0,
            "interval minimum product is not positive")
    roundup = artifact["directed_term_binary64_roundup_integrals"]
    rows = bridge["rows"]
    require([row["actual_node_composite"] for row in rows] == roundup,
            "repaired bridge node readback mismatch")
    for row in rows:
        require(row["assembled_upper"] ==
                row["actual_node_composite"] + row["coordinate_charge"] +
                row["panel_remainder"],
                "repaired bridge assembly mismatch")

    nodes = int(artifact["nodes"])
    span = int(artifact["span"])
    slices = [(start, min(start + span, nodes))
              for start in range(0, nodes, span)]
    require(slices[0] == (0, span), "partition start mismatch")
    require(slices[-1][1] == nodes, "partition end mismatch")
    require(all(left < right for left, right in slices),
            "empty partition span")
    require(all(slices[i][1] == slices[i + 1][0]
                for i in range(len(slices) - 1)),
            "partition gap or overlap")
    require(sum(right - left for left, right in slices) == nodes,
            "partition coverage mismatch")

    result = {
        "record": 2407,
        "status": "REPAIRED_FULL_GRID_SAME_EXPRESSION_AUDIT_PASS",
        "artifact": str(ARTIFACT.relative_to(ROOT)),
        "source_hashes_match": True,
        "nodes": nodes,
        "span": span,
        "workers": artifact["workers"],
        "span_count": len(slices),
        "same_expression_span_dominance": True,
        "same_expression_integral_dominance": True,
        "term_roundup_dominance": True,
        "partition_contiguous_full_coverage": True,
        "repaired_bridge_2408_readback": True,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2407_repaired_fullgrid_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
