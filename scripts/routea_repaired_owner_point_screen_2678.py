"""Price the actual repaired binary64 point owner against record 2675.

This is a decision probe only.  It reuses the committed 2677 factor chain,
replaces the analytic coefficient rectangles by exact binary64 point values,
rounds family rectangles outward to 160-bit dyadics, and checks the aggregate
against the stored record-2675 base-M0 rectangle.
"""

from __future__ import annotations

import importlib.util
import json
import struct
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CELL = ROOT / "results/2675_repaired_owner_cell_price_certificate.json"
OUT = ROOT / "results/2678_repaired_owner_point_screen.json"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def midpoint_float(ball: dict) -> float:
    midpoint = (Fraction(ball["lower_exact"]) + Fraction(ball["upper_exact"])) / 2
    return float(midpoint)


def bits(value: float) -> str:
    return f"0x{struct.unpack('>Q', struct.pack('>d', value))[0]:016x}"


def main() -> None:
    enc = load("enc2678", ROOT / "scripts/routea_cell4096_containment_2676.py")
    owner = load("owner2678", ROOT / "scripts/routea_corrected_strip_envelope_2303.py")
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    rows = repair["coefficient_rows"]
    base = [complex(midpoint_float(row["ideal_base_coefficient"]["real"]),
                    midpoint_float(row["ideal_base_coefficient"]["imag"]))
            for row in rows]
    families, _, _, anchors = owner.load_owner()
    width = enc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
    theta = enc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
        "capturedModulations2584")
    cell = json.loads(CELL.read_text(encoding="utf-8"))
    right_bits = int(cell["cell"]["cell_endpoints"]["x_hi"]["bits"], 16)
    right = enc.fraction_of_bits(right_bits)
    _, _, phi_lo, phi_hi = enc.exp_pins()
    per_family = enc.build_chain(families, base, base, right, theta, width,
                                 (phi_lo, phi_hi))
    family_rects = enc.channel_rects(per_family, base)[0]
    dyadic = [enc.dyadic_outer(rect, bits=160) for rect in family_rects]
    scale = 1 << 160
    aggregate = [sum(Fraction(rect[i], scale) for rect in dyadic)
                 for i in range(4)]
    exported = tuple(enc.fraction_of_bits(
        int(cell["cell"]["channels"][0]["rectangle_endpoints"][key]["bits"], 16))
        for key in ("re_lo", "re_hi", "im_lo", "im_hi"))
    inside = (exported[0] <= aggregate[0] <= exported[1] and
              exported[2] <= aggregate[2] <= exported[3])
    margins = {
        "re_lo": str(aggregate[0] - exported[0]),
        "re_hi": str(exported[1] - aggregate[1]),
        "im_lo": str(aggregate[2] - exported[2]),
        "im_hi": str(exported[3] - aggregate[3]),
    }
    report = {
        "record": 2678,
        "status": "REPAIRED_OWNER_POINT_SCREEN",
        "scope": "30 families, base M0, cell 4096",
        "owner_source": "2338 exact-interpolation midpoint cast to binary64",
        "family_count": len(family_rects),
        "family_rectangles_dyadic_bits": 160,
        "family_rectangles_dyadic": [[str(Fraction(value, 1 << 160))
                                      for value in rect] for rect in dyadic],
        "owner_bit_patterns": {
            "base": [{"real": bits(value.real), "imag": bits(value.imag)}
                     for value in base],
            "all_families_from_artifact": True,
        },
        "aggregate_exact": [str(value) for value in aggregate],
        "exported_record2675_exact": [str(value) for value in exported],
        "aggregate_inside_exported": inside,
        "aggregate_margins_exact": margins,
        "captured_family_anchors": anchors,
        "continuum_enclosure_proved": False,
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                   encoding="utf-8")
    print(json.dumps({key: report[key] for key in
                      ("record", "status", "family_count",
                       "aggregate_inside_exported", "aggregate_margins_exact")},
                     indent=2))


if __name__ == "__main__":
    main()
