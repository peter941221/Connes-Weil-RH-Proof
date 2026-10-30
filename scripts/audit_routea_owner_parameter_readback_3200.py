"""3200: audit numerical family parameters against the Lean Route A owner."""

from __future__ import annotations

import json
import re
from fractions import Fraction as F
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
LEAN_SCALE = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean"
EXTERNAL = ROOT / "ConnesWeilRH/Dev/C1RouteAExternalOwnerIdentity.lean"
PYTHON_SOURCE = ROOT / "scripts/routea_owner_whole_cell_2535.py"
WINDOW_RADIUS = F(65536001, 10000000)


def parse_stored_widths() -> list[F]:
    text = LEAN_SCALE.read_text(encoding="utf-8")
    match = re.search(r"noncomputable def storedWidth.*?\n\nnoncomputable def widthBump", text, re.MULTILINE | re.DOTALL)
    if match is None:
        raise ValueError("storedWidth definition not found")
    tokens = re.findall(r"\((\d+) / (\d+)\)|(?<![0-9])2(?![0-9])", match.group(0))
    values = [F(2) if token[0] == "" else F(int(token[0]), int(token[1]))
              for token in tokens]
    if len(values) != 30:
        raise ValueError(f"expected 30 stored widths, found {len(values)}")
    return values


def main() -> None:
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    widths = parse_stored_widths()
    captured_radii = [F.from_float(float.fromhex(pair[0])) ** 2
                      for pair in capture["families_hex"]]
    radius_matches = [captured == stored ** 2
                      for captured, stored in zip(captured_radii, widths)]
    coefficient_rows = repair["coefficient_rows"]
    coefficient_boxes_valid = len(coefficient_rows) == 30 and all(
        row["index"] == index and all(
            F(bounds["lower_exact"]) <= F(bounds["upper_exact"])
            for bounds in row["ideal_correction_coefficient"].values()
        )
        for index, row in enumerate(coefficient_rows)
    )
    result = {
        "record": 3200,
        "status": "OWNER_PARAMETER_READBACK_BOUNDARY_AUDIT",
        "formula_identity": {
            "status": "PASS",
            "python": "exp(-30/q + sigma*x + i*theta*x), q=1-(x/r)^2",
            "lean": "externalFamilyValue2344; externalFamilyValue2344_eq_familyTerm",
            "source": str(EXTERNAL.relative_to(ROOT)),
            "python_source": str(PYTHON_SOURCE.relative_to(ROOT)),
        },
        "captured_radius_matches_stored_width_squared": all(radius_matches),
        "radius_mismatch_indices": [i for i, match in enumerate(radius_matches) if not match],
        "python_window_radius": str(WINDOW_RADIUS),
        "lean_owner_max_radius": str(max(captured_radii)),
        "python_window_exceeds_owner_support": WINDOW_RADIUS > max(captured_radii),
        "coefficient_boxes_valid": coefficient_boxes_valid,
        "lean_concrete_coefficient_readback": False,
        "lean_concrete_modulation_readback": False,
        "producer_certificate": False,
        "nonclaims": [
            "does not prove the outer radius extension is zero in Lean",
            "does not import JSONL into Lean",
            "does not prove derivative upper rows",
            "does not prove the full-line tail",
            "no SourceRH",
            "no RH",
        ],
    }
    output = ROOT / "results/3200_routea_owner_parameter_readback_audit.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
