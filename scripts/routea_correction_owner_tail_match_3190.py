"""3190: audit correction-owner identity against the 2353 correction tail row."""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(1000000)


def run() -> dict:
    repair_path = ROOT / "results/2338_exact_interpolation_repair.json"
    capture_path = ROOT / "results/2275_gap_owner_audit.json"
    tail_path = ROOT / "results/2353_same_owner_tail_supplier.json"
    finite_path = ROOT / "results/3187_signed_taylor6_interval_40960.json"
    repair = json.loads(repair_path.read_text())
    capture = json.loads(capture_path.read_text())["owner_capture"]
    tail = json.loads(tail_path.read_text())
    finite = json.loads(finite_path.read_text())
    correction_rows = repair["coefficient_rows"]
    correction_tail_rows = tail["contour_family_bounds_T128"][1]
    correction_tail = sum((F(row["total_upper_exact"]) for row in correction_tail_rows), F(0))
    finite_upper = F(finite["total_upper"])
    combined = finite_upper + correction_tail
    same_repair = tail["input_sha256"]["results/2338_exact_interpolation_repair.json"] == hashlib.sha256(repair_path.read_bytes()).hexdigest()
    same_capture = tail["input_sha256"]["results/2275_gap_owner_audit.json"] == hashlib.sha256(capture_path.read_bytes()).hexdigest()
    return {
        "record": 3190,
        "status": "NUMERIC_CORRECTION_OWNER_TAIL_MATCHED_LEAN_OPEN",
        "coefficient_row_count": len(correction_rows),
        "family_count": len(capture["families_hex"]),
        "correction_tail_row_count": len(correction_tail_rows),
        "same_repair_input": same_repair,
        "same_capture_input": same_capture,
        "correction_tail_upper": str(correction_tail),
        "finite_window_upper": finite["total_upper"],
        "combined_numeric_upper": str(combined),
        "combined_numeric_upper_negative": combined < 0,
        "coefficient_owner_transfer_closed": same_repair and same_capture and len(correction_rows) == len(capture["families_hex"]),
        "signed_full_kernel_priced": False,
        "tail_supplier_imported_in_lean": False,
        "producer_go": False,
        "source_rh": False,
        "rh_claim": False,
        "scope": "correction coefficient-box and geometry identity audit; no Lean theorem",
        "input_sha256": {
            "results/2338_exact_interpolation_repair.json": hashlib.sha256(repair_path.read_bytes()).hexdigest(),
            "results/2275_gap_owner_audit.json": hashlib.sha256(capture_path.read_bytes()).hexdigest(),
            "results/2353_same_owner_tail_supplier.json": hashlib.sha256(tail_path.read_bytes()).hexdigest(),
            "results/3187_signed_taylor6_interval_40960.json": hashlib.sha256(finite_path.read_bytes()).hexdigest(),
        },
        "blocking_reasons": [
            "the correction tail supplier remains external",
            "the signed full-line kernel is not priced as one Lean object",
            "the numeric finite-window certificate is not imported into Lean",
        ],
    }


def main() -> None:
    output = ROOT / "results/3190_correction_owner_tail_match.json"
    result = run()
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "coefficient_owner_transfer_closed": result["coefficient_owner_transfer_closed"],
        "combined_numeric_upper_negative": result["combined_numeric_upper_negative"],
        "correction_tail_upper": result["correction_tail_upper"],
    }, indent=2))


if __name__ == "__main__":
    main()
