"""Record the exact owner-alignment obstruction found after record 2677.

The 2338 analytic midpoint cast to binary64 is the numerical repaired owner.
Record 2677's family rectangles were built from the 2338 coefficient boxes,
but the cast does not lie in those narrow boxes.  This script replays the
first family and reports the exact rational containment failure so that the
next certificate can be generated from the actual binary64 point owner.
"""

from __future__ import annotations

import json
import struct
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
SCREEN = ROOT / "results/2677_cell4096_coefficient_enclosure_screen.json"
OUT = ROOT / "results/2678_owner_alignment_no_go.json"


def bits_to_fraction(bits: int) -> Fraction:
    return Fraction.from_float(struct.unpack(">d", struct.pack(">Q", bits))[0])


def midpoint_bits(ball: dict) -> int:
    midpoint = (Fraction(ball["lower_exact"]) +
                Fraction(ball["upper_exact"])) / 2
    return struct.unpack(">Q", struct.pack(">d", float(midpoint)))[0]


def main() -> None:
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    screen = json.loads(SCREEN.read_text(encoding="utf-8"))
    row = repair["coefficient_rows"][0]["ideal_base_coefficient"]
    re_bits = midpoint_bits(row["real"])
    im_bits = midpoint_bits(row["imag"])
    re_value = bits_to_fraction(re_bits)
    im_value = bits_to_fraction(im_bits)
    re_lo = Fraction(row["real"]["lower_exact"])
    re_hi = Fraction(row["real"]["upper_exact"])
    im_lo = Fraction(row["imag"]["lower_exact"])
    im_hi = Fraction(row["imag"]["upper_exact"])
    failures = {
        "real_lower_gap": str(re_lo - re_value) if re_value < re_lo else "0",
        "real_upper_gap": str(re_value - re_hi) if re_value > re_hi else "0",
        "imag_lower_gap": str(im_lo - im_value) if im_value < im_lo else "0",
        "imag_upper_gap": str(im_value - im_hi) if im_value > im_hi else "0",
    }
    report = {
        "record": 2678,
        "status": "OWNER_ALIGNMENT_NO_GO",
        "scope": "family 0, base M0, cell 4096",
        "failure_mechanism": (
            "the binary64 cast of the 2338 analytic midpoint is outside the "
            "narrow 2338 coefficient rectangle; exact-center 2677 rectangles "
            "cannot be consumed by the repaired owner"
        ),
        "repaired_owner_bit_patterns": {
            "real": f"0x{re_bits:016x}",
            "imag": f"0x{im_bits:016x}",
        },
        "repaired_owner_exact": {"real": str(re_value), "imag": str(im_value)},
        "analytic_box": {
            "real_lo": str(re_lo), "real_hi": str(re_hi),
            "imag_lo": str(im_lo), "imag_hi": str(im_hi),
        },
        "exact_outside_gaps": failures,
        "2677_screen_provenance": screen["provenance"],
        "required_next_step": (
            "recompute all 30 family rectangles from the repaired binary64 "
            "point owner, prove their aggregate remains inside record 2675, "
            "then connect the resulting rectangles to the 2675 integral charge"
        ),
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8")
    print(json.dumps({k: report[k] for k in
                      ("record", "status", "scope", "repaired_owner_bit_patterns",
                       "exact_outside_gaps")}, indent=2))


if __name__ == "__main__":
    main()
