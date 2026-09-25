#!/usr/bin/env python3
"""Record 1979: preflight decision for the live four-point route."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CARDINAL = ROOT / "results" / "1959_cardinal_base_limitation.json"
DESIGN = ROOT / "results" / "1959_fourpoint_owner_density.json"
OUTPUT = ROOT / "results" / "1979_route_preflight.json"


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def main() -> None:
    cardinal = load(CARDINAL)
    design = load(DESIGN)
    profile = cardinal.get("contraction_profile", [])
    cardinal_max = max(profile) if profile else None
    cardinal_scan_failure = cardinal.get("T_need") is None and (
        cardinal_max is not None and cardinal_max > 0.5
    )

    candidates = []
    for row in design.get("cases", []):
        if row.get("C", 0.0) > 0.0 and row.get("B01", 0.0) > 0.0 \
                and row.get("det", 0.0) < 0.0:
            candidates.append({
                "tag": row["tag"],
                "C": row["C"],
                "b": row["B01"],
                "D": row["D"],
                "det": row["det"],
                "lambda": row.get("lam_vertex"),
                "contraction_T_need": row.get("contraction_T_need"),
                "contraction_max": row.get("contraction_max"),
                "route_spread_max": max(
                    row.get("spread_C", 0.0),
                    row.get("spread_B01", 0.0),
                    row.get("spread_D", 0.0),
                ),
                "cancel_ratio_max": row.get("cancel_ratio_max"),
            })

    report = {
        "record": 1979,
        "status": "PREFLIGHT_ONLY",
        "provenance": (
            "record 1979 preflight; inputs are committed record-1959 JSON "
            "artifacts produced by fourpoint_owner_density_1959.py"
        ),
        "inputs": [
            "results/1959_cardinal_base_limitation.json",
            "results/1959_fourpoint_owner_density.json",
        ],
        "scoped_no_go": {
            "old_cardinal_base": cardinal_scan_failure,
            "scope": "finite scanned range only; no all-height no-go",
            "reason": (
                "T_need is absent and the scanned contraction profile stays "
                "above 1/2"
            ) if cardinal_scan_failure else "not established",
            "min_contraction_profile": min(profile) if profile else None,
            "max_contraction_profile": cardinal_max,
            "mass_beyond_abs_xi_4": cardinal.get("mass_beyond", {}).get("4.0"),
        },
        "representative_sign_screen": {
            "rows": len(design.get("cases", [])),
            "sign_candidates": len(candidates),
            "candidates": candidates,
            "verdict": "SIGN_ONLY" if candidates else "NO_SIGN_CANDIDATE_IN_SAMPLE",
            "owner_warning": (
                "The design probe interpolates only eight target nodes, not "
                "healthyCorrectionNodes with the closed-ball zero prefix; "
                "its rho is a formal sample, not an established zeta zero."
            ),
        },
        "full_live_route": {
            "verdict": "INSUFFICIENT_EVIDENCE",
            "missing": [
                "actual admissible base transform and strip contraction",
                "complete healthyCorrectionNodes owner and node separation",
                "actual C4 and C2 decay constants",
                "same-owner tail ratio beta_s*L_n/(multiplicity*lambda^2)",
                "interval-certified bounds for C, b, and determinant",
            ],
        },
        "decision_rule": {
            "GO": "all missing fields have strict interval margins on one owner and one n",
            "SIGN_ONLY": "a representative point passes gate signs on the eight-node design owner",
            "INSUFFICIENT_EVIDENCE": "the full zero-prefix owner or another required field is unmeasured",
        },
    }
    OUTPUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
