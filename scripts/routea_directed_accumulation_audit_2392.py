"""Audit the stored 2385 directed-accumulation artifact.

This is a replay-integrity check, not a Lean numerical import.  It verifies
the artifact's own source hashes, channel alignment, directed-roundup
dominance, and the exact readback used by the 2386 bridge.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> dict:
    fullgrid_path = ROOT / "results/2385_shared_geometry_776611.json"
    bridge_path = ROOT / "results/2386_composite_charge_bridge.json"
    fullgrid = json.loads(fullgrid_path.read_text())
    bridge = json.loads(bridge_path.read_text())

    source_path = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator_path = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    require(fullgrid["source_sha256"] == sha256(source_path),
            "2359 source hash mismatch")
    require(fullgrid["evaluator_source_sha256"] == sha256(evaluator_path),
            "2242 evaluator source hash mismatch")

    mpfr = fullgrid["directed_mpfr_term_accumulation_integrals"]
    roundup = fullgrid["directed_term_binary64_roundup_integrals"]
    require(len(mpfr) == len(roundup) == 4, "four-channel shape mismatch")
    require(fullgrid["directed_term_binary64_roundup_dominates_mpfr"] ==
            [roundup[i] >= mpfr[i] for i in range(4)],
            "stored dominance flags do not read back")
    for index, (mpfr_value, roundup_value) in enumerate(zip(mpfr, roundup)):
        require(math.isfinite(mpfr_value) and math.isfinite(roundup_value),
                f"non-finite channel {index}")
        require(mpfr_value >= 0 and roundup_value >= mpfr_value,
                f"roundup does not dominate channel {index}")

    rows = bridge["rows"]
    require([row["channel"] for row in rows] ==
            ["base_M0", "base_D2", "corr_M0", "corr_D2"],
            "bridge channel order mismatch")
    for index, row in enumerate(rows):
        require(row["actual_node_composite"] == roundup[index],
                f"bridge readback mismatch at channel {index}")
        assembled = (row["actual_node_composite"] +
                     row["coordinate_charge"] + row["panel_remainder"])
        require(assembled == row["assembled_upper"],
                f"assembled upper mismatch at channel {index}")

    corr_d2 = rows[3]
    result = {
        "record": 2392,
        "status": "DIRECTED_ACCUMULATION_ARTIFACT_INVARIANTS_PASS",
        "fullgrid_record": fullgrid["record"],
        "bridge_record": bridge["record"],
        "source_hashes_match": True,
        "four_channel_shape": True,
        "roundup_dominates_mpfr": True,
        "bridge_readback_matches_roundup": True,
        "corr_D2_assembled_upper": corr_d2["assembled_upper"],
        "lean_numeric_imported": False,
        "directed_accumulation_theorem_proved": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2392_directed_accumulation_artifact_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
