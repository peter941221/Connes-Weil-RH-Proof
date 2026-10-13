"""Generate the cell-1024 repaired-owner correction-M0 bridge."""

from __future__ import annotations

import importlib.util
import json
import re
import struct
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2687_repaired_owner_2048_grid_screen.json"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CALC = ROOT / "scripts/routea_cell4096_containment_2676.py"
BASE_GENERATOR = ROOT / "scripts/generate_routea_cell1024_base_m0_2688.py"
BASE_OWNER = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2688BaseM0.lean"
BASE_CONSUMER = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2688BaseM0Consumer.lean"
OUT = ROOT / "ConnesWeilRH/Dev"

CELL_INDEX = 1024
CELL_RIGHT = "0x3f7a36e2eb1c4400"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bits(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def coefficient_definition(rows: list[dict]) -> str:
    entries = []
    for row in rows:
        coeff = row["ideal_correction_coefficient"]
        real = (Fraction(coeff["real"]["lower_exact"]) +
                Fraction(coeff["real"]["upper_exact"])) / 2
        imag = (Fraction(coeff["imag"]["lower_exact"]) +
                Fraction(coeff["imag"]["upper_exact"])) / 2
        entries.append((bits(float(real)), bits(float(imag))))
    body = ",\n".join(
        f"    ⟨binary64Value2674 {real}, binary64Value2674 {imag}⟩"
        for real, imag in entries
    )
    return (
        "noncomputable def record2689CorrectionCoefficient : Fin 30 → ℂ :=\n"
        "  ![\n" + body + "]\n\n"
    )


def rect_literal(rects: list[tuple[int, ...]]) -> str:
    lines = [
        "noncomputable def record2678CorrectionM0FamilyRects : Fin 30 → ComplexRect2427 :=",
        "  ![",
    ]
    for index, row in enumerate(rects):
        args = " ".join(f"(({value} : ℚ) / (2 : ℚ) ^ 160 : ℝ)" for value in row)
        suffix = "," if index < len(rects) - 1 else "]"
        lines.append(f"    ComplexRect2427.mk {args}{suffix}")
    return "\n".join(lines) + "\n\n"


def replace_once(source: str, pattern: str, replacement: str, label: str) -> str:
    updated, count = re.subn(pattern, replacement, source, count=1, flags=re.DOTALL)
    if count != 1:
        raise RuntimeError(f"could not replace {label}")
    return updated


def build() -> None:
    calc = load("routea_calc_2689", CALC)
    base_gen = load("routea_base_generator_2689", BASE_GENERATOR)
    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    row = artifact["cells_data"][CELL_INDEX]
    if row[0] != CELL_INDEX or row[2] != CELL_RIGHT:
        raise ValueError("record 2687 cell 1024 endpoint bits changed")
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    repair_rows = repair["coefficient_rows"]

    correction = []
    for item in repair_rows:
        coeff = item["ideal_correction_coefficient"]
        real = (Fraction(coeff["real"]["lower_exact"]) +
                Fraction(coeff["real"]["upper_exact"])) / 2
        imag = (Fraction(coeff["imag"]["lower_exact"]) +
                Fraction(coeff["imag"]["upper_exact"])) / 2
        correction.append(type("Coeff", (), {"real": float(real), "imag": float(imag)})())

    widths = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
    thetas = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
        "capturedModulations2584")
    right = calc.fraction_of_bits(int(CELL_RIGHT, 16))
    per_family = calc.build_chain(
        [], correction, correction, right, thetas, widths, calc.exp_pins()[2:])
    correction_rects = calc.channel_rects(per_family, correction)[0]
    dyadic = [base_gen.dyadic_rect(rect) for rect in correction_rects]
    exported = tuple(calc.fraction_of_bits(int(value, 16)) for value in row[5][2][:4])
    aggregate = tuple(Fraction(sum(box[i] for box in dyadic), 1 << 160)
                      for i in range(4))
    if not all((aggregate[0] > exported[0], aggregate[1] < exported[1],
                aggregate[2] > exported[2], aggregate[3] < exported[3])):
        raise ValueError("cell 1024 correction_M0 analytic aggregate escapes artifact rectangle")

    owner = BASE_OWNER.read_text(encoding="utf-8")
    owner = owner.replace("BaseM0", "CorrectionM0")
    owner = owner.replace("record2688BaseCoefficient", "record2689CorrectionCoefficient")
    owner = replace_once(
        owner,
        r"noncomputable def record2689CorrectionCoefficient : Fin 30 → ℂ :=.*?\n\nnoncomputable def record2688CorrectionM0FamilyRects",
        coefficient_definition(repair_rows) + "noncomputable def record2688CorrectionM0FamilyRects",
        "correction coefficient definition",
    )
    owner = replace_once(
        owner,
        r"noncomputable def record2688CorrectionM0FamilyRects : Fin 30 → ComplexRect2427 :=.*?\ndef record2688CorrectionM0AggregateReLo : ℚ :=.*?\nnoncomputable def record2688CorrectionM0Aggregate : ComplexRect2427 :=",
        rect_literal(dyadic).replace("record2678", "record2688")
        + base_gen.aggregate_defs(dyadic).replace("record2678", "record2688")
        .replace("BaseM0", "CorrectionM0").split(
            "noncomputable def record2688CorrectionM0Aggregate : ComplexRect2427 :=\n", 1
        )[0]
        + "noncomputable def record2688CorrectionM0Aggregate : ComplexRect2427 :=",
        "family rectangles and exact aggregate",
    )
    cell_args = " ".join(f"(binary64Value2674 {value} : ℝ)" for value in row[5][2][:4])
    cell_def = (
        "noncomputable def record2688CorrectionM0Rect : ComplexRect2427 :=\n"
        f"  ComplexRect2427.mk {cell_args}\n\n"
    )
    owner = replace_once(
        owner,
        r"noncomputable def record2688CorrectionM0Rect : ComplexRect2427 :=.*?\n\n",
        cell_def,
        "cell artifact rectangle",
    )
    owner = owner.replace("record2688CorrectionM0", "record2689CorrectionM0")
    owner_path = OUT / "C1RouteARepairedOwnerCell2689CorrectionM0.lean"
    owner_path.write_text(owner, encoding="utf-8", newline="\n")

    consumer = BASE_CONSUMER.read_text(encoding="utf-8")
    consumer = consumer.replace(
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCellCharge2686",
        "import ConnesWeilRH.Dev.C1RouteACellIntegralCharge2675",
    )
    consumer = consumer.replace("Cell2688BaseM0", "Cell2689CorrectionM0")
    consumer = consumer.replace("BaseM0", "CorrectionM0")
    consumer = consumer.replace("record2688BaseCoefficient", "record2689CorrectionCoefficient")
    consumer = consumer.replace("record2688CorrectionM0", "record2689CorrectionM0")
    norm_bits, charge_bits = row[5][2][4], row[5][2][5]
    consumer = re.sub(
        r"def record2689CorrectionM0Norm : ℝ := binary64Value2674 0x[0-9a-fA-F]+",
        f"def record2689CorrectionM0Norm : ℝ := binary64Value2674 {norm_bits}",
        consumer,
    )
    consumer = re.sub(
        r"def record2689CorrectionM0Charge : ℝ := binary64Value2674 0x[0-9a-fA-F]+",
        f"def record2689CorrectionM0Charge : ℝ := binary64Value2674 {charge_bits}",
        consumer,
    )
    consumer = consumer.replace(
        "C1RouteARepairedOwnerCell2688CorrectionM0",
        "C1RouteARepairedOwnerCell2689CorrectionM0",
    )
    consumer_path = OUT / "C1RouteARepairedOwnerCell2689CorrectionM0Consumer.lean"
    consumer_path.write_text(consumer, encoding="utf-8", newline="\n")

    audit = """import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2689CorrectionM0Consumer

namespace ConnesWeilRH.Dev

#print axioms record2689CorrectionM0AggregateFamilySumEq
#print axioms record2689CorrectionM0AggregateSubset
#print axioms record2689CorrectionM0CellContained
#print axioms record2689CorrectionM0CellContainedForIntegral
#print axioms record2689CorrectionM0IntegralCharge

end ConnesWeilRH.Dev
"""
    (OUT / "C1RouteARepairedOwnerCell2689CorrectionM0Audit.lean").write_text(
        audit, encoding="utf-8", newline="\n")
    print("generated cell 1024 correction-M0 bridge", len(dyadic), "families")


if __name__ == "__main__":
    build()
