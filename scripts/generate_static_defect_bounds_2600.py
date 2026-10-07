"""Generate the finite rational defect-bound comparison for record 2600."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"
WITNESS = ROOT / "results/2351_moment_matrix_witness.json"
OUTPUT = DEV / "C1RouteACorrectionStaticDefectBounds2600.lean"
COMMON_OUTPUT = DEV / "C1RouteACorrectionStaticDefectBounds2600Common.lean"
PAYLOAD_CHUNK_ROWS = 10


def real_expr(value: str) -> str:
    fraction = Fraction(value)
    if fraction.denominator == 1:
        return f"({fraction.numerator} : ℝ)"
    return f"(({fraction.numerator} : ℝ) / {fraction.denominator})"


def point_rect(entry: dict) -> str:
    re_value = entry["real"]["lower_exact"]
    im_value = entry["imag"]["lower_exact"]
    return (
        "{ reLo := " + real_expr(re_value) +
        ",\n        reHi := " + real_expr(re_value) +
        ",\n        imLo := " + real_expr(im_value) +
        ",\n        imHi := " + real_expr(im_value) + " }"
    )


def interval_rect(entry: dict) -> str:
    return (
        "{ reLo := " + real_expr(entry["real"]["lower_exact"]) +
        ",\n        reHi := " + real_expr(entry["real"]["upper_exact"]) +
        ",\n        imLo := " + real_expr(entry["imag"]["lower_exact"]) +
        ",\n        imHi := " + real_expr(entry["imag"]["upper_exact"]) + " }"
    )


def fin_literal(index: int) -> str:
    if index == 0:
        return "0"
    return f"(Fin.succ {fin_literal(index - 1)})"


def interval_product(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    values = [left_lower * right_lower
              for left_lower in left for right_lower in right]
    return min(values), max(values)


def interval_add(left: tuple[Fraction, Fraction], right: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def interval_neg(value: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return -value[1], -value[0]


def product_rect(left: dict, right: dict) -> str:
    left_real = (Fraction(left["real"]["lower_exact"]), Fraction(left["real"]["upper_exact"]))
    left_imag = (Fraction(left["imag"]["lower_exact"]), Fraction(left["imag"]["upper_exact"]))
    right_real = (Fraction(right["real"]["lower_exact"]), Fraction(right["real"]["upper_exact"]))
    right_imag = (Fraction(right["imag"]["lower_exact"]), Fraction(right["imag"]["upper_exact"]))
    real = interval_add(interval_product(left_real, right_real),
                        interval_neg(interval_product(left_imag, right_imag)))
    imag = interval_add(interval_product(left_real, right_imag),
                        interval_product(left_imag, right_real))
    return (
        "{ reLo := " + real_expr(str(real[0])) +
        ",\n        reHi := " + real_expr(str(real[1])) +
        ",\n        imLo := " + real_expr(str(imag[0])) +
        ",\n        imHi := " + real_expr(str(imag[1])) + " }"
    )


def cell_theorem(i: int, j: int, candidate_names: list[str], analytic_names: list[str], bridge_names: list[str], matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    name = f"candidateInverseDefectEntryBound2600_cell_{i:02d}_{j:02d}"
    candidate_bridge = f"candidateInverseInterval2600_apply_row_{i:02d}"
    analytic_bridges = ", ".join(
        f"analyticMomentInterval2597_apply_row_{row:02d}" for row in range(30)
    )
    row_index = fin_literal(i)
    column_index = fin_literal(j)
    product_lemmas = []
    product_names = []
    for k in range(30):
        product_name = f"hmul_{k:02d}"
        product_names.append(product_name)
        product_lemmas.append(f'''  have {product_name} :
      (candidateInverseInterval2600 {row_index} {fin_literal(k)}).mul
        (analyticMomentInterval2597 {fin_literal(k)} {column_index}) =
      {product_rect(inverse[i][k], matrix[k][j])} := by
    change ComplexRect2427.mul ({point_rect(inverse[i][k]).replace(chr(10), " ")} : ComplexRect2427) ({interval_rect(matrix[k][j]).replace(chr(10), " ")} : ComplexRect2427) =
      {product_rect(inverse[i][k], matrix[k][j])}
    norm_num [ComplexRect2427.mul,
      RealInterval2429.add, RealInterval2429.mul, RealInterval2429.sub,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
''')
    product_names_text = ", ".join(product_names)
    return f'''set_option maxHeartbeats 0 in
 theorem {name} :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 {row_index} {column_index}) ≤
      analyticDefectEntryBounds2595 {row_index} {column_index} := by
{chr(10).join(product_lemmas)}
  simp only [matrixDefectInterval2598,
    matrixProductInterval2598, ComplexRect2427.sumFinset,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk]
  rw [{product_names_text}]
  rw [← NNReal.coe_le_coe]
  norm_num [rectL1Upper2598, analyticDefectEntryBounds2595,
    ComplexRect2427.point, ComplexRect2427.sub,
    Matrix.cons_val_zero, Matrix.cons_val_one]
'''


def row_module(i: int, candidate_names: list[str], analytic_names: list[str], bridge_names: list[str], matrix: list[list[dict]], inverse: list[list[dict]]) -> str:
    from generate_static_coordinate_bounds_2617 import CONVERTED_ROWS, row_facade_source
    if i in CONVERTED_ROWS:
        return row_facade_source(i)
    cells = []
    dispatch = []
    for j in range(30):
        cells.append(cell_theorem(i, j, candidate_names, analytic_names, bridge_names, matrix, inverse))
        dispatch.append(
            f"  · exact candidateInverseDefectEntryBound2600_cell_{i:02d}_{j:02d}"
        )
    row_name_text = f"candidateInverseDefectEntryBound2600_row_{i:02d}"
    return f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common

/-! Fixed-row cell comparisons for record 2600, row {i:02d}. -/

namespace ConnesWeilRH.Dev

{chr(10).join(cells)}

theorem {row_name_text}
    (j : Fin 30) :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 {i} j) ≤
      analyticDefectEntryBounds2595 {i} j := by
  fin_cases j
{chr(10).join(dispatch)}

end ConnesWeilRH.Dev
'''


def main() -> None:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    if len(inverse) != 30 or any(len(row) != 30 for row in inverse):
        raise ValueError("expected a 30 by 30 candidate inverse")

    row_names = [f"candidateInverseInterval2600_row_{i:02d}" for i in range(30)]
    entry_names = [
        [f"candidateInverseInterval2600_entry_{i:02d}_{j:02d}" for j in range(30)]
        for i in range(30)
    ]
    row_names_text = ",\n    ".join(row_names)
    analytic_names = [
        f"analyticMomentInterval2597_row_{i:02d}" for i in range(30)
    ]
    bridge_names = []
    payload_modules = []
    for chunk_start in range(0, 30, PAYLOAD_CHUNK_ROWS):
        chunk_end = min(chunk_start + PAYLOAD_CHUNK_ROWS, 30)
        module_name = (
            "C1RouteACorrectionStaticDefectBounds2600Payload"
            f"Rows{chunk_start:02d}{chunk_end - 1:02d}"
        )
        payload_modules.append(module_name)
        payload_defs = []
        for i in range(chunk_start, chunk_end):
            for j in range(30):
                payload_defs.append(
                    f'''/-! Candidate-inverse point rectangle for record 2600, entry ({i:02d},{j:02d}). -/

noncomputable def {entry_names[i][j]} : ComplexRect2427 :=
  {point_rect(inverse[i][j])}
'''
                )
        payload_text = f'''import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

/-! Candidate-inverse point rectangles for record 2600, rows {chunk_start:02d}..{chunk_end - 1:02d}. -/

namespace ConnesWeilRH.Dev

{chr(10).join(payload_defs)}
end ConnesWeilRH.Dev
'''
        (DEV / f"{module_name}.lean").write_text(
            payload_text, encoding="utf-8", newline="\n"
        )
    payload_imports = "\n".join(
        f"import ConnesWeilRH.Dev.{module}" for module in payload_modules
    )
    row_defs = []
    for i, row_name in enumerate(row_names):
        row_defs.append(
            f"noncomputable def {row_name} : Fin 30 → ComplexRect2427 :=\n"
            "  ![" + ",\n    ".join(entry_names[i]) + "]\n"
        )
    common_text = f'''import ConnesWeilRH.Dev.C1RouteACorrectionIntervalPropagation2598
import ConnesWeilRH.Dev.C1RouteACorrectionDefectEntryBounds2595
{payload_imports}

/-! Shared exact point rectangles for record 2600. -/

namespace ConnesWeilRH.Dev

{chr(10).join(row_defs)}

noncomputable def candidateInverseInterval2600 :
    Matrix (Fin 30) (Fin 30) ComplexRect2427 :=
  ![{row_names_text}]

end ConnesWeilRH.Dev
'''
    COMMON_OUTPUT.write_text(common_text, encoding="utf-8", newline="\n")

    row_modules = []
    for i, row_name in enumerate(row_names):
        module_name = f"C1RouteACorrectionStaticDefectBounds2600Row{i:02d}"
        row_modules.append(module_name)
        (DEV / f"{module_name}.lean").write_text(
            row_module(i, row_names, analytic_names, bridge_names, matrix, inverse),
            encoding="utf-8",
            newline="\n",
        )
        if i == 0:
            from generate_static_coordinate_bounds_2617 import generated_row_sources
            for filename, source in generated_row_sources(payload).items():
                (DEV / filename).write_text(source, encoding="utf-8", newline="\n")

    imports = "\n".join(
        f"import ConnesWeilRH.Dev.{module}" for module in row_modules
    )
    dispatch = "\n".join(
        f"  · exact candidateInverseDefectEntryBound2600_row_{i:02d} j"
        for i in range(30)
    )
    facade = f'''{imports}

/-! Facade for the split finite rational comparison at record 2600. -/

namespace ConnesWeilRH.Dev

theorem candidateInverseDefectEntryBound2600
    (i j : Fin 30) :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 i j) ≤
      analyticDefectEntryBounds2595 i j := by
  fin_cases i
{dispatch}

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(facade, encoding="utf-8", newline="\n")
    print(json.dumps({
        "record": 2600,
        "rows": 30,
        "entries": 900,
        "cell_theorems": 900,
        "row_modules": len(row_modules),
        "common_output": str(COMMON_OUTPUT.relative_to(ROOT)),
        "witness_sha256": hashlib.sha256(WITNESS.read_bytes()).hexdigest(),
        "output": str(OUTPUT.relative_to(ROOT)),
    }, indent=2))


if __name__ == "__main__":
    main()
