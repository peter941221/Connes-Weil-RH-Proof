"""Current-source audit for the captured-owner full-grid interface.

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
STRIP_LOADER = ROOT / "scripts/routea_corrected_strip_envelope_2303.py"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR_REREAD = ROOT / "results/2665_l1_margin_repair.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(artifact_path: Path = ARTIFACT, bridge_path: Path = BRIDGE,
         output_path: Path | None = None, record: int = 2426) -> dict:
    artifact = json.loads(artifact_path.read_text())
    bridge = json.loads(bridge_path.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    repair_reread = json.loads(REPAIR_REREAD.read_text())
    source = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    worker_source = source.read_text(encoding="utf-8")
    loader_source = STRIP_LOADER.read_text(encoding="utf-8")
    require(artifact["source_sha256"] == sha256(source), "worker hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator),
            "evaluator hash mismatch")
    require(artifact["nodes"] == 776611 and artifact["span"] == 20001,
            "unexpected replay dimensions")
    require(artifact["workers"] == 16, "unexpected worker count")
    require(artifact["exact_binary64_audit_enabled"], "exact audit disabled")
    require('"2275_gap_owner_audit.json"' in loader_source,
            "owner loader no longer points to the audited capture")
    require("strip.load_owner()" in worker_source,
            "full-grid worker no longer loads the strip owner")
    require("2338_exact_interpolation_repair.json" not in worker_source,
            "worker unexpectedly refers to repaired coefficients")
    capture_hashes = {"base": capture["base_md5"],
                      "correction": capture["corr_md5"]}
    control_hashes = {"base": repair_reread["control"]["base_md5"],
                      "correction": repair_reread["control"]["corr_md5"]}
    repaired_hashes = {"base": repair_reread["treatment"]["base_md5"],
                       "correction": repair_reread["treatment"]["corr_md5"]}
    require(capture_hashes == control_hashes,
            "2665 control is not the 2275 captured owner")
    require(capture_hashes != repaired_hashes,
            "expected the 2338 repaired treatment to change coefficients")
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
        "status": "CAPTURED_OWNER_INTERFACE_PASS_REPAIR_TRANSFER_OPEN",
        "artifact": str(artifact_path.relative_to(ROOT)),
        "bridge": str(bridge_path.relative_to(ROOT)),
        "source_hashes_match": True,
        "owner_source": "2275 captured coefficients",
        "capture_hashes": capture_hashes,
        "2665_control_hashes": control_hashes,
        "2665_repaired_treatment_hashes": repaired_hashes,
        "captured_owner_matches_2665_control": True,
        "captured_owner_matches_repaired_treatment": False,
        "nodes": artifact["nodes"],
        "span": artifact["span"],
        "span_count": len(rows),
        "same_expression_controls_pass": True,
        "current_parent_and_span_bridge_match": True,
        "pointwise_mathematical_term_dominance_proved": False,
        "repaired_owner_fullgrid_replayed": False,
        "captured_window_ratio_is_repaired_owner_bound": False,
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
