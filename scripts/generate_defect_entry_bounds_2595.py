"""Generate the 2351 Fraction defect-entry NNReal payload for Lean."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_moment_matrix_exact_check_2351 as checker

WITNESS = ROOT / "results/2351_moment_matrix_witness.json"
CHECK = ROOT / "results/2351_moment_matrix_exact_check.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionDefectEntryBounds2595.lean"


def nnreal_expr(value: Fraction) -> str:
    if value < 0:
        raise ValueError("NNReal bound is negative")
    return f"(({value.numerator} : NNReal) / {value.denominator})"


def main():
    payload = json.loads(WITNESS.read_text())
    matrix = [[checker.complex_interval(value) for value in row] for row in payload["matrix"]]
    inverse = [[checker.complex_interval(value) for value in row] for row in payload["candidate_inverse"]]
    dimension = len(matrix)
    if dimension != 30 or any(len(row) != dimension for row in matrix + inverse):
        raise ValueError("expected 30 by 30 matrix and inverse")
    product = [[checker.sum_complex(
        checker.complex_mul(inverse[row][index], matrix[index][column])
        for index in range(dimension))
        for column in range(dimension)]
        for row in range(dimension)]
    defect = [[checker.complex_add(checker.point(int(row == column)),
                                  checker.complex_neg(product[row][column]))
               for column in range(dimension)]
              for row in range(dimension)]
    bounds = [[checker.l1_upper(value) for value in row] for row in defect]
    row_sums = [sum(row, Fraction(0)) for row in bounds]
    parent = json.loads(CHECK.read_text())
    if [str(value) for value in row_sums] != parent["row_bounds_exact"]:
        raise ValueError("generated row sums differ from the committed 2351 row bounds")

    row_names = [f"analyticDefectEntryBounds2595_row_{index:02d}" for index in range(dimension)]
    row_defs = []
    for name, row in zip(row_names, bounds):
        row_defs.append(
            f"/-- Row payload for `{name}`. -/\n"
            f"noncomputable def {name} : Fin 30 → NNReal :=\n"
            f"  ![" + ", ".join(nnreal_expr(value) for value in row) + "]\n"
        )
    row_defs_text = "\n".join(row_defs)
    matrix_literal = ",\n    ".join(row_names)

    row_sum_theorems = []
    for index, name in enumerate(row_names):
        row_sum_theorems.append(
            f"set_option maxHeartbeats 0 in\n"
            f"theorem analyticDefectEntryBounds2595_row_sum_{index:02d} :\n"
            f"    (∑ j : Fin 30, {name} j) =\n"
            f"      analyticDefectRowBounds2593 {index} := by\n"
            f"  simp [{name}, analyticDefectRowBounds2593, Fin.sum_univ_succ]\n"
            f"  norm_num\n"
        )
    row_sum_theorems_text = "\n".join(row_sum_theorems)

    row_sum_dispatch = []
    for index in range(dimension):
        row_sum_dispatch.append(
            f"  · simpa [analyticDefectEntryBounds2595] using\n"
            f"      analyticDefectEntryBounds2595_row_sum_{index:02d}"
        )
    row_sum_dispatch_text = "\n".join(row_sum_dispatch)

    source_hash = hashlib.sha256(WITNESS.read_bytes()).hexdigest()
    text = f'''import ConnesWeilRH.Dev.C1RouteACorrectionRowBounds2593

/-! Exact nonnegative defect-entry upper bounds reconstructed from the 2351
Fraction witness. They bound the exported interval defect in the L1 row norm;
they do not assert that Lean's analytic matrix has these entries. -/

namespace ConnesWeilRH.Dev

{row_defs_text}

/-- Entrywise NNReal bounds for the 30 by 30 Neumann defect payload. -/
noncomputable def analyticDefectEntryBounds2595 :
    Matrix (Fin 30) (Fin 30) NNReal :=
  ![{matrix_literal}]

{row_sum_theorems_text}

theorem analyticDefectEntryBounds2595_row_sum
    (i : Fin 30) :
    (∑ j : Fin 30, analyticDefectEntryBounds2595 i j) =
      analyticDefectRowBounds2593 i := by
  fin_cases i
{row_sum_dispatch_text}

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8")
    print(json.dumps({
        "record": 2595,
        "rows": 30,
        "entries": 900,
        "witness_sha256": source_hash,
        "output": str(OUTPUT.relative_to(ROOT)),
    }, indent=2))


if __name__ == "__main__":
    main()
