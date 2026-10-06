"""Rewrite one 2600 row module to consume its exact product cache."""

import re
import json
from fractions import Fraction
from pathlib import Path

from generate_static_defect_bounds_2600 import (
    WITNESS,
    interval_add,
    interval_neg,
    interval_product,
    fin_literal,
    real_expr,
)


ROOT = Path(__file__).resolve().parents[1]
ROW = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionStaticDefectBounds2600Row00.lean"
PRODUCT_IMPORT = "import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectProductCache2600Row00"


def product_coords(left: dict, right: dict) -> dict[str, Fraction]:
    left_real = (Fraction(left["real"]["lower_exact"]), Fraction(left["real"]["upper_exact"]))
    left_imag = (Fraction(left["imag"]["lower_exact"]), Fraction(left["imag"]["upper_exact"]))
    right_real = (Fraction(right["real"]["lower_exact"]), Fraction(right["real"]["upper_exact"]))
    right_imag = (Fraction(right["imag"]["lower_exact"]), Fraction(right["imag"]["upper_exact"]))
    real = interval_add(
        interval_product(left_real, right_real),
        interval_neg(interval_product(
            left_imag, right_imag)),
    )
    imag = interval_add(
        interval_product(left_real, right_imag),
        interval_product(left_imag, right_real),
    )
    return {"reLo": real[0], "reHi": real[1], "imLo": imag[0], "imHi": imag[1]}


def final_comparison(column: int, matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    column_index = fin_literal(column)
    names = ", ".join(f"hmul_{inner:02d}" for inner in range(30))
    sums = []
    for coordinate in ("reLo", "reHi", "imLo", "imHi"):
        total = sum(
            (product_coords(inverse[0][inner], matrix[inner][column])[coordinate]
             for inner in range(30)),
            Fraction(0),
        )
        sums.append(f'''  have hsum_{coordinate} :
      (∑ k : Fin 30, ((candidateInverseInterval2600 0 k).mul
        (analyticMomentInterval2597 k {column_index})).{coordinate}) =
      {real_expr(str(total))} := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
    rw [{names}]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
''')
    defect = f"(matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 {column_index})"
    return "".join(sums) + f'''  apply NNReal.coe_le_coe.mp
  change
    (max |{defect}.reLo| |{defect}.reHi| +
      max |{defect}.imLo| |{defect}.imHi|) {chr(8804)}
      (analyticDefectEntryBounds2595 0 {column_index} : ℝ)
  rw [matrixDefectInterval2598_reLo, matrixDefectInterval2598_reHi,
    matrixDefectInterval2598_imLo, matrixDefectInterval2598_imHi]
  rw [hsum_reHi, hsum_reLo, hsum_imHi, hsum_imLo]
  norm_num [analyticDefectEntryBounds2595,
    Matrix.cons_val_zero, Matrix.cons_val_one]
'''


def rewrite_cell(match: re.Match[str]) -> str:
    column = int(match.group("column"))
    body = match.group("body")
    names = re.findall(r"  have (hmul_\d{2}) :", body)
    replacements = []
    for name in names:
        inner = int(name[-2:])
        theorem = f"candidateInverseAnalyticProduct2600_00_{column:02d}_{inner:02d}"
        replacements.append(f"  have {name} := {theorem}\n")
    return "".join(replacements)


def main() -> None:
    text = ROW.read_text(encoding="utf-8")
    if "hsum_reLo" in text:
        print(f"row already uses cached final comparisons: {ROW}")
        return
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    if PRODUCT_IMPORT not in text:
        text = text.replace(
            "import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common",
            "import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common\n" + PRODUCT_IMPORT,
            1,
        )
    cells = re.compile(
        r"(?P<head>set_option maxHeartbeats 0 in\n theorem candidateInverseDefectEntryBound2600_cell_00_(?P<column>\d{2}) .*? := by\n)"
        r"(?P<body>.*?)(?=\n  simp only \[matrixDefectInterval2598,)",
        re.DOTALL,
    )
    rewritten, count = cells.subn(
        lambda match: match.group("head") + rewrite_cell(match),
        text,
    )
    if count != 30:
        raise RuntimeError(f"expected 30 cells, rewrote {count}")
    cell_bodies = re.compile(
        r"(?P<head>set_option maxHeartbeats 0 in\n theorem candidateInverseDefectEntryBound2600_cell_00_(?P<column>\d{2}) .*? := by\n)"
        r"(?P<body>.*?)(?=\n\s*set_option maxHeartbeats 0 in\n theorem|\n\s*theorem candidateInverseDefectEntryBound2600_row_00)",
        re.DOTALL,
    )

    def rewrite_final(match: re.Match[str]) -> str:
        body = match.group("body")
        marker = "  simp only [matrixDefectInterval2598,"
        position = body.index(marker)
        return (
            match.group("head")
            + body[:position]
            + final_comparison(int(match.group("column")), payload["matrix"], payload["candidate_inverse"])
        )

    rewritten, final_count = cell_bodies.subn(rewrite_final, rewritten)
    if final_count != 30:
        raise RuntimeError(f"expected 30 final comparisons, rewrote {final_count}")
    ROW.write_text(rewritten, encoding="utf-8")
    print(f"rewrote {count} cells in {ROW}")


if __name__ == "__main__":
    main()
