"""Independent readback for the 2411 retained span witnesses.

This verifies artifact shape, provenance, and finite/nonnegative witnesses.
It intentionally does not claim mathematical-term dominance or Lean import.
The two accumulation conventions are reported separately: parent reduction
then one ``dx`` multiplication versus one ``dx`` multiplication per span.
"""

from __future__ import annotations

import hashlib
import json
import math
import argparse
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2411_repaired_shared_geometry_776611.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(artifact_path: Path = ARTIFACT, output_path: Path | None = None,
         record: int = 2411) -> dict:
    artifact = json.loads(artifact_path.read_text())
    source = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    require(artifact["source_sha256"] == sha256(source),
            f"{record} source hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator),
            f"{record} evaluator hash mismatch")
    require(artifact["nodes"] == 776611 and artifact["span"] == 20001,
            "unexpected replay dimensions")

    rows = artifact["directed_term_binary64_roundup_span_integrals"]
    require(len(rows) == 39, "expected 39 span witnesses")
    expected_lengths = [20001] * 38 + [16573]
    actual_lengths = [min((index + 1) * artifact["span"], artifact["nodes"])
                      - index * artifact["span"] for index in range(len(rows))]
    require(actual_lengths == expected_lengths, "span lengths do not cover replay")
    require(all(len(row) == 4 for row in rows), "span channel width mismatch")
    require(all(math.isfinite(value) and value >= 0
                 for row in rows for value in row),
            "non-finite or negative span witness")

    parent = artifact["directed_term_binary64_roundup_integrals"]
    span_sum = [math.fsum(row[channel] for row in rows) for channel in range(4)]
    exact_input_sum = [
        sum((Fraction.from_float(row[channel]) for row in rows), Fraction(0))
        for channel in range(4)
    ]
    exact_gaps = [
        exact_input_sum[channel] - Fraction.from_float(parent[channel])
        for channel in range(4)
    ]
    result = {
        "record": record,
        "status": "REPAIRED_SPAN_WITNESS_READBACK_PASS",
        "source_hashes_match": True,
        "nodes": artifact["nodes"],
        "span": artifact["span"],
        "span_count": len(rows),
        "span_lengths": actual_lengths,
        "witnesses_finite_nonnegative": True,
        "parent_roundup_integrals": parent,
        "span_sum_integrals": span_sum,
        "span_input_exact_sum": [str(value) for value in exact_input_sum],
        "span_sum_minus_parent_exact": [str(value) for value in exact_gaps],
        "pointwise_mathematical_term_dominance_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = output_path or (ROOT / f"results/{record}_span_witness_audit.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--record", type=int, default=2411)
    args = parser.parse_args()
    main(args.artifact if args.artifact.is_absolute() else ROOT / args.artifact,
         args.output if args.output is None or args.output.is_absolute() else ROOT / args.output,
         args.record)
