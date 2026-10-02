"""Check the stored index-4 owner coefficient against Lean's exact literals."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
LEAN = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(record: int = 2439) -> dict:
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))
    owner = capture["owner_capture"]
    source = LEAN.read_text(encoding="utf-8")
    base = owner["base_hex"][4]
    corr = owner["corr_hex"][4]
    expected = {
        "storedBaseFour": (
            Fraction(-2679001875721701, 262144),
            Fraction(-3001940793386885, 4194304),
        ),
        "storedCorrFour": (
            Fraction(-6001732121601347, 32),
            Fraction(-3369790430725407, 64),
        ),
    }
    observed = {
        "storedBaseFour": tuple(Fraction.from_float(float.fromhex(v)) for v in base),
        "storedCorrFour": tuple(Fraction.from_float(float.fromhex(v)) for v in corr),
    }
    require(observed == expected, "stored index-4 coefficient differs")
    for numerator in (
        "-2679001875721701 / 262144",
        "-3001940793386885 / 4194304",
        "-6001732121601347 / 32",
        "-3369790430725407 / 64",
    ):
        require(numerator in source, f"missing Lean literal: {numerator}")
    result = {
        "record": record,
        "status": "OWNER_FOUR_COEFFICIENT_IDENTITY_PASS",
        "capture_sha256": sha256(CAPTURE),
        "lean_source_sha256": sha256(LEAN),
        "checked_index": 4,
        "base_hex": base,
        "corr_hex": corr,
        "all_coefficients_imported_into_lean": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / f"results/{record}_stored_owner_four_identity_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
