"""Audit the ordered span partition used by the 2385 replay.

The check binds the reconstructed contiguous slices to the 2359 source hash.
It proves only the index partition/readback invariant; it does not prove
pointwise term dominance or import a numeric value into Lean.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> dict:
    fullgrid_path = ROOT / "results/2385_shared_geometry_776611.json"
    fullgrid = json.loads(fullgrid_path.read_text())
    source_path = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    require(fullgrid["source_sha256"] == sha256(source_path),
            "2359 source hash mismatch")

    nodes = int(fullgrid["nodes"])
    span = int(fullgrid["span"])
    require(nodes > 0 and span > 0, "non-positive partition dimensions")
    slices = [(start, min(start + span, nodes))
              for start in range(0, nodes, span)]
    require(slices and slices[0] == (0, min(span, nodes)),
            "partition does not start at zero")
    require(all(left < right for left, right in slices),
            "empty span in partition")
    require(all(slices[index][1] == slices[index + 1][0]
                for index in range(len(slices) - 1)),
            "gap or overlap in ordered spans")
    require(slices[-1][1] == nodes, "partition does not end at nodes")
    require(sum(right - left for left, right in slices) == nodes,
            "span lengths do not cover node count")

    result = {
        "record": 2394,
        "status": "DIRECTED_SPAN_PARTITION_AUDIT_PASS",
        "source_hash_matches": True,
        "nodes": nodes,
        "span": span,
        "span_count": len(slices),
        "first_span": list(slices[0]),
        "last_span": list(slices[-1]),
        "contiguous_no_overlap": True,
        "full_coverage": True,
        "lean_partition_imported": False,
        "numeric_term_dominance_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2394_directed_span_partition_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
