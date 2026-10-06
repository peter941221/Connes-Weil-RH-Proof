"""Validate the frozen 2338 family widths against the Lean owner source."""

from fractions import Fraction
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
LEAN_SOURCE = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean"


def parse_stored_widths(source: str):
    block = source.split("noncomputable def storedWidth", 1)[1].split(
        "noncomputable def widthBump", 1
    )[0]
    block = block.split(":=", 1)[1]
    values = []
    for token in re.findall(r"\((\d+) / (\d+)\)|(?<![\d/])(\d+)(?![\d/])", block):
        numerator, denominator, integer = token
        values.append(
            Fraction(int(integer))
            if integer
            else Fraction(int(numerator), int(denominator))
        )
    return values


def main():
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    captured_widths = [
        Fraction.from_float(float.fromhex(width))
        for width, _modulation in capture["families_hex"]
    ]
    stored_widths = parse_stored_widths(LEAN_SOURCE.read_text(encoding="utf-8"))
    if len(captured_widths) != 30 or len(stored_widths) != 30:
        raise AssertionError("expected exactly 30 owner families")
    mismatches = [
        index
        for index, (captured, stored) in enumerate(zip(captured_widths, stored_widths))
        if captured != stored
    ]
    result = {
        "record": 2584,
        "status": "OWNER_WIDTH_ALIGNMENT_PASS" if not mismatches else "OWNER_WIDTH_ALIGNMENT_FAIL",
        "capture_source": str(CAPTURE.relative_to(ROOT)),
        "lean_source": str(LEAN_SOURCE.relative_to(ROOT)),
        "family_count": len(captured_widths),
        "width_mismatches": mismatches,
        "radius_convention": "Lean radius is storedWidth[index]^2; 2338 uses width^2",
        "modulations_instantiated": False,
        "nodes_instantiated": False,
        "targets_instantiated": False,
        "membership_theorem": False,
        "owner_transfer_to_live_consumer": False,
        "producer_go": False,
        "rh_claim": False,
    }
    if mismatches:
        raise AssertionError(json.dumps(result, indent=2))
    output = ROOT / "results/2584_owner_parameter_alignment.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
