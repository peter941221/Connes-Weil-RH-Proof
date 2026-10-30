"""3203: replay the concrete Route A owner parameter readback."""

from __future__ import annotations

import json
import re
import struct
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
PARAMETERS = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean"
OWNER = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCorrectionM02680.lean"


def binary64_fraction(bits: str) -> F:
    value = struct.unpack(">d", int(bits, 16).to_bytes(8, "big"))[0]
    return F.from_float(value)


def parse_modulations() -> list[F]:
    text = PARAMETERS.read_text(encoding="utf-8")
    body = re.search(
        r"noncomputable def capturedModulations2584 : Fin 30 → ℝ :=\n\s*!\[(.*?)\n\nnoncomputable def capturedNodes2584",
        text,
        re.DOTALL,
    )
    if body is None:
        raise ValueError("capturedModulations2584 body not found")
    values: list[F] = []
    for token in re.findall(r"\(\((-?\d+) : ℝ\) / (\d+)\)|\((0) : ℝ\)", body.group(1)):
        if token[2]:
            values.append(F(0))
        else:
            values.append(F(int(token[0]), int(token[1])))
    if len(values) != 30:
        raise ValueError(f"expected 30 modulation values, found {len(values)}")
    return values


def parse_owner_coefficients() -> list[tuple[F, F]]:
    text = OWNER.read_text(encoding="utf-8")
    body = re.search(
        r"noncomputable def record2680CorrectionCoefficient : Fin 30 → ℂ :=\n\s*!\[(.*?)\n\nset_option maxRecDepth",
        text,
        re.DOTALL,
    )
    if body is None:
        raise ValueError("record2680CorrectionCoefficient body not found")
    values = [
        (binary64_fraction(real_bits), binary64_fraction(imag_bits))
        for real_bits, imag_bits in re.findall(
            r"binary64Value2674 0x([0-9a-f]+), binary64Value2674 0x([0-9a-f]+)",
            body.group(1),
        )
    ]
    if len(values) != 30:
        raise ValueError(f"expected 30 owner coefficients, found {len(values)}")
    return values


def main() -> None:
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))["coefficient_rows"]
    owner_coefficients = parse_owner_coefficients()
    owner_modulations = parse_modulations()

    modulation_matches = [
        F.from_float(float.fromhex(pair[1])) == owner_modulations[index]
        for index, pair in enumerate(capture["families_hex"])
    ]
    coefficient_membership = []
    for index, (real_value, imag_value) in enumerate(owner_coefficients):
        box = repair[index]["ideal_correction_coefficient"]
        real_bounds = F(box["real"]["lower_exact"]), F(box["real"]["upper_exact"])
        imag_bounds = F(box["imag"]["lower_exact"]), F(box["imag"]["upper_exact"])
        coefficient_membership.append(
            real_bounds[0] <= real_value <= real_bounds[1]
            and imag_bounds[0] <= imag_value <= imag_bounds[1]
        )

    result = {
        "record": 3203,
        "status": "CONCRETE_OWNER_PARAMETER_READBACK_AUDIT",
        "owner_coefficient_source": str(OWNER.relative_to(ROOT)),
        "owner_modulation_source": str(PARAMETERS.relative_to(ROOT)),
        "all_30_modulations_match_capture": all(modulation_matches),
        "modulation_mismatch_indices": [i for i, ok in enumerate(modulation_matches) if not ok],
        "all_30_owner_coefficients_in_correction_boxes": all(coefficient_membership),
        "coefficient_box_mismatch_indices": [i for i, ok in enumerate(coefficient_membership) if not ok],
        "readback_semantics": {
            "modulations": "exact equality of captured binary64 lifts",
            "coefficients": "exact owner binary64 values lie inside 2338 correction boxes",
            "not_claimed": "box centers are not treated as owner coefficients",
        },
        "producer_certificate": False,
        "nonclaims": [
            "does not prove the Taylor coefficient upper rows in Lean",
            "does not import JSONL into Lean",
            "does not prove the full-line tail",
            "no SourceRH",
            "no RH",
        ],
    }
    output = ROOT / "results/3203_routea_concrete_owner_parameter_readback.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()