"""Generate the finite rational defect-bound comparison for record 2600."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WITNESS = ROOT / "results/2351_moment_matrix_witness.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionStaticDefectBounds2600.lean"


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
        "\n        reHi := " + real_expr(re_value) +
        "\n        imLo := " + real_expr(im_value) +
        "\n        imHi := " + real_expr(im_value) + " }"
    )


def main() -> None:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    inverse = payload["candidate_inverse"]
    if len(inverse) != 30 or any(len(row) != 30 for row in inverse):
        raise ValueError("expected a 30 by 30 candidate inverse")
    row_names = [f"candidateInverseInterval2600_row_{i:02d}" for i in range(30)]
    row_defs = []
    for name, row in zip(row_names, inverse):
        row_defs.append(
            f"/-- Exact point rectangles for `{name}`. -/\n"
            f"noncomputable def {name} : Fin 30 → ComplexRect2427 :=\n"
            "  ![" + ",\n    ".join(point_rect(entry) for entry in row) + "]\n"
        )
    row_names_text = ",\n    ".join(row_names)
    all_defs = ", ".join(row_names + [
        f"analyticMomentInterval2597_row_{i:02d}" for i in range(30)
    ])
    row_theorems = []
    for i, name in enumerate(row_names):
        row_theorems.append(
            f"set_option maxHeartbeats 0 in\n"
            f"theorem candidateInverseDefectEntryBound2600_row_{i:02d}\n"
            f"    (j : Fin 30) :\n"
            f"    rectL1Upper2598 (matrixDefectInterval2598\n"
            f"      candidateInverseInterval2600 analyticMomentInterval2597 {i} j) ≤\n"
            f"      analyticDefectEntryBounds2595 {i} j := by\n"
            f"  fin_cases j <;> norm_num [rectL1Upper2598, matrixDefectInterval2598,\n"
            f"    matrixProductInterval2598, candidateInverseInterval2600,\n"
            f"    analyticMomentInterval2597, analyticDefectEntryBounds2595,\n"
            f"    {all_defs}]\n"
        )
    dispatch = []
    for i in range(30):
        dispatch.append(
            f"  · exact candidateInverseDefectEntryBound2600_row_{i:02d} j"
        )
    source_hash = hashlib.sha256(WITNESS.read_bytes()).hexdigest()
    text = f'''import ConnesWeilRH.Dev.C1RouteACorrectionIntervalPropagation2598
import ConnesWeilRH.Dev.C1RouteACorrectionDefectEntryBounds2595

/-! Finite rational comparison between the propagated 2351 candidate-inverse
rectangles and the imported 2595 defect-entry payload. This file does not prove
that the analytic rectangles contain the actual integral entries. -/

namespace ConnesWeilRH.Dev

{chr(10).join(row_defs)}

noncomputable def candidateInverseInterval2600 :
    Matrix (Fin 30) (Fin 30) ComplexRect2427 :=
  ![{row_names_text}]

{chr(10).join(row_theorems)}

theorem candidateInverseDefectEntryBound2600
    (i j : Fin 30) :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 i j) ≤
      analyticDefectEntryBounds2595 i j := by
  fin_cases i
{chr(10).join(dispatch)}

end ConnesWeilRH.Dev
'''
    OUTPUT.write_text(text, encoding="utf-8", newline="\n")
    print(json.dumps({
        "record": 2600,
        "rows": 30,
        "entries": 900,
        "witness_sha256": source_hash,
        "output": str(OUTPUT.relative_to(ROOT)),
    }, indent=2))


if __name__ == "__main__":
    main()
