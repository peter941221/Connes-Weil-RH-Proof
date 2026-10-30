"""3189: fail-closed numeric bridge from the finite window to the tail."""

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
    finite_path = ROOT / "results/3187_signed_taylor6_interval_40960.json"
    tail_path = ROOT / "results/2353_same_owner_tail_supplier.json"
    finite = json.loads(finite_path.read_text())
    tail = json.loads(tail_path.read_text())
    finite_upper = F(finite["total_upper"])
    tail_upper = F(tail["contour_base_upper_T128_exact"])
    combined = finite_upper + tail_upper
    return {
        "record": 3189,
        "status": "NUMERIC_FINITE_TAIL_MARGIN_PROMISING_OWNER_TRANSFER_OPEN",
        "finite_window_upper": str(finite_upper),
        "external_tail_upper": str(tail_upper),
        "combined_numeric_upper": str(combined),
        "combined_numeric_upper_negative": combined < 0,
        "same_owner_transfer_closed": False,
        "full_signed_kernel_priced": False,
        "tail_supplier_imported_in_lean": False,
        "producer_go": False,
        "source_rh": False,
        "rh_claim": False,
        "scope": "numeric scale check only; 2353 tail is not paired to 3187 correction owner",
        "input_sha256": {
            "results/3187_signed_taylor6_interval_40960.json": hashlib.sha256(finite_path.read_bytes()).hexdigest(),
            "results/2353_same_owner_tail_supplier.json": hashlib.sha256(tail_path.read_bytes()).hexdigest(),
        },
        "blocking_reasons": [
            "the finite-window correction owner is not transferred into the 2353 tail theorem",
            "the tail is not imported into Lean",
            "the full signed kernel remains unpriced",
        ],
    }


def main() -> None:
    output = ROOT / "results/3189_correction_finite_tail_bridge.json"
    result = run()
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "record": result["record"],
        "status": result["status"],
        "combined_numeric_upper_negative": result["combined_numeric_upper_negative"],
        "artifact": str(output),
    }, indent=2))


if __name__ == "__main__":
    main()
