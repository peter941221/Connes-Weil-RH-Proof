"""Price cell 4096 with the certified coefficient rectangles from record 2338.

This screen replaces each midpoint-cast coefficient by its exact rational
lower/upper enclosure before the family products are formed. It checks whether
the wider family boxes still fit the exported record-2675 rectangles. The
result is numerical design evidence; Lean must prove both the coefficient-box
bridge and the continuous family containment.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import struct
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CELL_ARTIFACT = ROOT / "results/2675_repaired_owner_cell_price_certificate.json"
OUTPUT = ROOT / "results/2677_cell4096_coefficient_enclosure_screen.json"
LEAN_OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACellContainment2677Aggregates.lean"
MIDPOINT_SCREEN = ROOT / "results/2676_cell4096_containment_screen.json"
MIDPOINT_GENERATOR = ROOT / "scripts/routea_cell4096_containment_2676.py"
PRICE_GENERATOR = ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py"
OWNER_GENERATOR = ROOT / "scripts/routea_corrected_strip_envelope_2303.py"
DYADIC_BITS = 160

CHANNELS = {
    "base_M0": ("record2675BaseM0Rect", "record2675BaseM0Norm"),
    "base_D2": ("record2675BaseD2Rect", "record2675BaseD2Norm"),
    "correction_M0": ("record2675CorrectionM0Rect", "record2675CorrectionM0Norm"),
    "correction_D2": ("record2675CorrectionD2Rect", "record2675CorrectionD2Norm"),
}


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_coefficient_rectangles(rows: list[dict], field: str):
    rectangles = []
    for row in rows:
        value = row[field]
        coordinates = []
        for part in ("real", "imag"):
            coordinates.extend((
                Fraction(value[part]["lower_exact"]),
                Fraction(value[part]["upper_exact"]),
            ))
        rectangles.append(tuple(coordinates))
    return rectangles


def fraction_strings(values):
    return [str(value) for value in values]


def channel_rectangles(box_module, per_family, coefficient_boxes):
    k0 = []
    k2 = []
    for family, coefficient_box in zip(per_family, coefficient_boxes):
        mid = (
            box_module.RImul(family["phi_box"], family["cos_box"])[0],
            box_module.RImul(family["phi_box"], family["cos_box"])[1],
            box_module.RImul(family["phi_box"], family["sin_box"])[0],
            box_module.RImul(family["phi_box"], family["sin_box"])[1],
        )
        k0.append(box_module.CRmul(coefficient_box, mid))
        k2.append(box_module.CRmul(
            box_module.CRmul(coefficient_box, mid), family["factor_rect"]))
    return k0, k2


def midpoint_coefficients(price_module, rows, field: str):
    values = []
    for row in rows:
        value = row[field]
        components = []
        for part in ("real", "imag"):
            midpoint = (Fraction(value[part]["lower_exact"])
                        + Fraction(value[part]["upper_exact"])) / 2
            components.append(float(midpoint))
        values.append(complex(*components))
    return values


def render_aggregate_lean(report: dict) -> None:
    lines = [
        "import ConnesWeilRH.Dev.C1RouteACellContainment2676Aggregates",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
        "",
        "/- Record 2677 widens each 2676 midpoint coefficient to its exact",
        "   record-2338 coefficient rectangle. The coordinate aggregate can",
        "   exceed the narrower 2675 rectangle; these are the norm charges",
        "   consumed by the integral bridge. -/",
        "",
        "theorem fin30SumChain2677 {α : Type*} [AddCommMonoid α]",
        "    (f : Fin 30 → α) :",
        "    (∑ i : Fin 30, f i) =",
        "      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +",
        "      (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 +",
        "      (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 +",
        "      (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + f 29",
        "      )))))))))))))))))))))))))))) := by",
        "  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]",
        "  rfl",
        "",
    ]
    for name, (outer, norm_bound) in CHANNELS.items():
        channel = report["channels"][name]
        family_name = "record2677" + "".join(part.title() for part in name.split("_")) + "FamilyRects"
        aggregate_name = family_name.removesuffix("FamilyRects") + "Aggregate"
        coord_names = []
        lines.extend([f"noncomputable def {family_name} : Fin 30 → ComplexRect2427 :=", "  !["])
        for index, box in enumerate(channel["family_rectangles_dyadic_160"]):
            coords = [
                f"({value} : ℚ) / (2 : ℚ) ^ {DYADIC_BITS}"
                for value in box
            ]
            suffix = "," if index < 29 else "]"
            lines.append(
                "    ComplexRect2427.mk " + " ".join(f"({coord} : ℝ)" for coord in coords)
                + suffix
            )
        lines.append("")
        aggregate_coordinates = channel["aggregate_dyadic_160"]
        for field, value in zip(("ReLo", "ReHi", "ImLo", "ImHi"), aggregate_coordinates):
            coordinate = aggregate_name + field
            coord_names.append(coordinate)
            lines.extend([
                f"def {coordinate} : ℚ :=",
                f"  ({value} : ℚ) / (2 : ℚ) ^ {DYADIC_BITS}",
            ])
        lines.extend([
            f"noncomputable def {aggregate_name} : ComplexRect2427 :=",
            f"  ComplexRect2427.mk ({coord_names[0]} : ℝ)",
            f"    ({coord_names[1]} : ℝ)",
            f"    ({coord_names[2]} : ℝ)",
            f"    ({coord_names[3]} : ℝ)",
            "",
            f"theorem {aggregate_name}FamilySumEq :",
            f"    ComplexRect2427.sumFinset {family_name} Finset.univ = {aggregate_name} := by",
            "  ext <;> simp only [ComplexRect2427.sumFinset]",
            "  all_goals rw [fin30SumChain2677]",
            f"  all_goals simp [{family_name}]",
            f"  all_goals norm_num [{family_name}, {aggregate_name},",
            *[f"    {coordinate}," for coordinate in coord_names],
            "    binary64Value2674, binary64ExponentBits2674,",
            "    binary64Significand2674, binary64FractionBits2674,",
            "    binary64Sign2674]",
            "",
            f"theorem {aggregate_name}CornerNormLe :",
            f"    {aggregate_name}.cornerNorm ≤ {norm_bound} := by",
            "  apply ComplexRect2427.cornerNorm_le_of_sq_le",
            f"  · norm_num [{norm_bound}, binary64Value2674,",
            "      binary64ExponentBits2674, binary64Significand2674,",
            "      binary64FractionBits2674, binary64Sign2674]",
            f"  · norm_num [{aggregate_name}, ComplexRect2427.cornerNormSq,",
            *[f"      {coordinate}," for coordinate in coord_names],
            f"      {norm_bound}, binary64Value2674, binary64ExponentBits2674,",
            "      binary64Significand2674, binary64FractionBits2674,",
            "      binary64Sign2674]",
            "",
        ])
    lines.append("end ConnesWeilRH.Dev")
    LEAN_OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    enclosure = load_module("enclosure2677", MIDPOINT_GENERATOR)
    price = load_module("price2677", PRICE_GENERATOR)
    owner = load_module("owner2677", OWNER_GENERATOR)

    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    rows = repair["coefficient_rows"]
    base_boxes = exact_coefficient_rectangles(rows, "ideal_base_coefficient")
    correction_boxes = exact_coefficient_rectangles(rows, "ideal_correction_coefficient")

    base_midpoints = midpoint_coefficients(price, rows, "ideal_base_coefficient")
    correction_midpoints = midpoint_coefficients(price, rows, "ideal_correction_coefficient")
    base_hash = price.md5_complex(base_midpoints)
    correction_hash = price.md5_complex(correction_midpoints)

    capture = json.loads(price.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    reread = json.loads(price.REPAIR_REREAD.read_text(encoding="utf-8"))
    cell_artifact = json.loads(CELL_ARTIFACT.read_text(encoding="utf-8"))
    expected_hashes = {
        "base": reread["treatment"]["base_md5"],
        "correction": reread["treatment"]["corr_md5"],
    }
    midpoint_hashes = {"base": base_hash, "correction": correction_hash}
    if midpoint_hashes != expected_hashes:
        raise AssertionError("2338 midpoint casts do not match repaired treatment")
    if cell_artifact["owner_coefficients_md5"] != midpoint_hashes:
        raise AssertionError("2675 cell certificate has a different coefficient owner")

    families, _base, _correction, anchors = owner.load_owner()
    cell = cell_artifact["cell"]
    if cell_artifact["cell_index"] != 4096 or cell_artifact["partition_cells"] != 8192:
        raise AssertionError("expected cell 4096 of the 8192-cell partition")
    x_hi_bits = int(cell["cell_endpoints"]["x_hi"]["bits"], 16)
    cell_right = enclosure.fraction_of_bits(x_hi_bits)

    width_path = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean"
    modulation_path = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean"
    width_values = enclosure.parse_fin30_rationals(width_path, "storedWidth")
    theta_values = enclosure.parse_fin30_rationals(modulation_path, "capturedModulations2584")
    width_match = all(
        struct.pack(">d", float(width_values[i]))
        == struct.pack(">d", families[i][0]) for i in range(30))
    theta_match = all(
        float(theta_values[i]) == families[i][1] for i in range(30))
    if not width_match or not theta_match:
        raise AssertionError("Lean width/modulation literals differ from captured owner")

    _, _, phi_lo_base, phi_hi_pin = enclosure.exp_pins()
    per_family = enclosure.build_chain(
        families, base_midpoints, correction_midpoints, cell_right,
        theta_values, width_values, (phi_lo_base, phi_hi_pin))
    base_m0, base_d2 = channel_rectangles(enclosure, per_family, base_boxes)
    correction_m0, correction_d2 = channel_rectangles(
        enclosure, per_family, correction_boxes)

    exact_midpoint_base = enclosure.channel_rects(per_family, base_midpoints)
    exact_midpoint_correction = enclosure.channel_rects(per_family, correction_midpoints)
    midpoint_channels = {
        "base_M0": exact_midpoint_base[0],
        "base_D2": exact_midpoint_base[1],
        "correction_M0": exact_midpoint_correction[0],
        "correction_D2": exact_midpoint_correction[1],
    }
    coefficient_channels = {
        "base_M0": base_m0,
        "base_D2": base_d2,
        "correction_M0": correction_m0,
        "correction_D2": correction_d2,
    }

    exported = {}
    for row in cell["channels"]:
        endpoints = row["rectangle_endpoints"]
        exported[row["name"]] = tuple(
            enclosure.fraction_of_bits(int(endpoints[key]["bits"], 16))
            for key in ("re_lo", "re_hi", "im_lo", "im_hi"))

    report = {
        "record": 2677,
        "status": "CELL4096_COEFFICIENT_ENCLOSURE_SCREEN",
        "cell_index": 4096,
        "partition_cells": 8192,
        "cell_right_bits": f"0x{x_hi_bits:016x}",
        "coefficient_input": "exact lower/upper rational bounds from record 2338",
        "provenance": {
            "repair_sha256": sha256(REPAIR),
            "capture_sha256": sha256(price.CAPTURE),
            "2675_certificate_sha256": sha256(CELL_ARTIFACT),
            "midpoint_owner_md5": midpoint_hashes,
            "capture_owner_md5": {
                "base": capture["base_md5"],
                "correction": capture["corr_md5"],
            },
            "coefficient_interval_contains_midpoint_cast": all(
                box[0] <= Fraction.from_float(value.real) <= box[1]
                and box[2] <= Fraction.from_float(value.imag) <= box[3]
                for boxes, values in ((base_boxes, base_midpoints),
                                      (correction_boxes, correction_midpoints))
                for box, value in zip(boxes, values)),
            "width_bitwise_match": width_match,
            "modulation_bitwise_match": theta_match,
            "captured_families_bitwise_anchors": {
                key: anchors[key] for key in ("families_bitwise", "base_bitwise", "corr_bitwise")
            },
            "actual_live_owner_identity_proved": False,
        },
        "channels": {},
        "family_inputs": [],
    }
    for index, family in enumerate(per_family):
        report["family_inputs"].append({
            "index": index,
            "radius_exact": str(width_values[index] ** 2),
            "modulation_exact": str(theta_values[index]),
            "phi_interval_exact": fraction_strings(family["phi_box"]),
            "cos_interval_exact": fraction_strings(family["cos_box"]),
            "sin_interval_exact": fraction_strings(family["sin_box"]),
            "factor_rectangle_exact": fraction_strings(family["factor_rect"]),
            "base_coefficient_rectangle_exact": fraction_strings(base_boxes[index]),
            "correction_coefficient_rectangle_exact": fraction_strings(
                correction_boxes[index]),
        })
    exported_channel_rows = {row["name"]: row for row in cell["channels"]}
    for name, rectangles in coefficient_channels.items():
        family_boxes = [enclosure.dyadic_outer(rectangle, bits=DYADIC_BITS)
                        for rectangle in rectangles]
        scale = 1 << DYADIC_BITS
        family_rectangles = [tuple(Fraction(value, scale) for value in box)
                             for box in family_boxes]
        aggregate = enclosure.aggregate(family_rectangles)
        inside, margins = enclosure.containment(aggregate, exported[name])
        midpoint_aggregate = enclosure.aggregate(midpoint_channels[name])
        midpoint_inside, midpoint_margins = enclosure.containment(
            midpoint_aggregate, exported[name])
        norm_bits = int(
            exported_channel_rows[name]["corner_norm_chain"]["norm_upper"]["result"]["bits"], 16)
        norm_bound = enclosure.fraction_of_bits(norm_bits)
        corner_norm_sq = (
            max(abs(aggregate[0]), abs(aggregate[1])) ** 2
            + max(abs(aggregate[2]), abs(aggregate[3])) ** 2)
        report["channels"][name] = {
            "aggregate_exact": [str(value) for value in aggregate],
            "aggregate_float": [float(value) for value in aggregate],
            "aggregate_dyadic_160": [sum(box[k] for box in family_boxes)
                                     for k in range(4)],
            "exported_exact": [str(value) for value in exported[name]],
            "inside_exported": inside,
            "margin_ulps": margins,
            "norm_upper_bits": f"0x{norm_bits:016x}",
            "norm_upper_exact": str(norm_bound),
            "corner_norm_squared_exact": str(corner_norm_sq),
            "corner_norm_sq_le_norm_upper_sq": corner_norm_sq <= norm_bound ** 2,
            "norm_sq_slack_exact": str(norm_bound ** 2 - corner_norm_sq),
            "same_run_midpoint_control": {
                "aggregate_exact": [str(value) for value in midpoint_aggregate],
                "inside_exported": midpoint_inside,
                "margin_ulps": midpoint_margins,
            },
            "family_rectangles_dyadic_160": family_boxes,
        }

    report["coordinate_containment_pass"] = all(
        row["inside_exported"] for row in report["channels"].values())
    report["norm_budget_pass"] = all(
        row["corner_norm_sq_le_norm_upper_sq"]
        for row in report["channels"].values())
    report["status"] = (
        "CELL4096_COEFFICIENT_ENCLOSURE_NORM_PASS"
        if report["norm_budget_pass"] else "CELL4096_COEFFICIENT_ENCLOSURE_NORM_FAIL")
    OUTPUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    render_aggregate_lean(report)
    print("status:", report["status"])
    for name, channel in report["channels"].items():
        print(name, "inside=", channel["inside_exported"],
              "margin_ulps=", channel["margin_ulps"],
              "norm_pass=", channel["corner_norm_sq_le_norm_upper_sq"])


if __name__ == "__main__":
    main()
