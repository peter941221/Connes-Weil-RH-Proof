"""3295: combine the 3294 finite-window replay with the 2353 tail row."""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def run(manifest_path: Path, tail_path: Path) -> dict:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    tail = json.loads(tail_path.read_text(encoding="utf-8"))
    tail_rows = tail["contour_family_bounds_T128"][1]
    tail_upper = sum((F(row["total_upper_exact"]) for row in tail_rows), F(0))
    finite_upper = F(manifest["total_upper"])
    combined = finite_upper + tail_upper
    return {
        "record": 3295,
        "status": "EXTERNAL_FINITE_PLUS_TAIL_REPLAYED_LEAN_SIGNED_KERNEL_OPEN",
        "finite_manifest_record": manifest["record"],
        "finite_window_upper": str(finite_upper),
        "correction_tail_upper": str(tail_upper),
        "combined_numeric_upper": str(combined),
        "combined_numeric_upper_negative": combined < 0,
        "block_manifest_replayed": manifest["aggregate_replay_exact"],
        "finite_lean_endpoint_dominance_closed": manifest["lean_endpoint_dominance_closed"],
        "tail_supplier_imported_in_lean": False,
        "signed_full_kernel_priced": False,
        "producer_go": False,
        "source_rh": False,
        "rh_claim": False,
        "input_sha256": {
            str(manifest_path): hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
            str(tail_path): hashlib.sha256(tail_path.read_bytes()).hexdigest(),
        },
        "nonclaims": [
            "finite and tail values remain external rational replay evidence",
            "the Lean rational endpoint dominance premise is open",
            "the signed full-line kernel is not one imported Lean object",
            "no producer_go",
            "no SourceRH",
            "no RH",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=ROOT / "results/3294_routea_weighted_original_block_manifest.json")
    parser.add_argument("--tail", type=Path, default=ROOT / "results/2353_same_owner_tail_supplier.json")
    parser.add_argument("--output", type=Path, default=ROOT / "results/3295_routea_block_tail_match.json")
    args = parser.parse_args()
    result = run(args.manifest, args.tail)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("record", "status", "finite_window_upper", "correction_tail_upper", "combined_numeric_upper", "combined_numeric_upper_negative")}, indent=2))


if __name__ == "__main__":
    main()
