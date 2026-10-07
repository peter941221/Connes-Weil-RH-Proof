"""Generate a single-cell consumer probe for the Row00 sum blocks."""

import json
from fractions import Fraction

from generate_static_defect_bounds_2600 import (
    DEV,
    WITNESS,
    interval_add,
    interval_neg,
    interval_product,
    fin_literal,
    real_expr,
)


def product_coords(left: dict, right: dict) -> dict[str, Fraction]:
    left_real = (Fraction(left["real"]["lower_exact"]), Fraction(left["real"]["upper_exact"]))
    left_imag = (Fraction(left["imag"]["lower_exact"]), Fraction(left["imag"]["upper_exact"]))
    right_real = (Fraction(right["real"]["lower_exact"]), Fraction(right["real"]["upper_exact"]))
    right_imag = (Fraction(right["imag"]["lower_exact"]), Fraction(right["imag"]["upper_exact"]))
    real = interval_add(interval_product(left_real, right_real),
                        interval_neg(interval_product(left_imag, right_imag)))
    imag = interval_add(interval_product(left_real, right_imag),
                        interval_product(left_imag, right_real))
    return {"reLo": real[0], "reHi": real[1], "imLo": imag[0], "imHi": imag[1]}


def main() -> None:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    sums = {
        coordinate: sum(
            (product_coords(inverse[0][inner], matrix[inner][0])[coordinate] for inner in range(30)),
            Fraction(0),
        )
        for coordinate in ("reLo", "reHi", "imLo", "imHi")
    }
    hsum = []
    for coordinate in ("reLo", "reHi", "imLo", "imHi"):
        blocks = ", ".join(
            f"candidateInverseAnalyticSumBlock2600_00_00_{block}_{coordinate}"
            for block in range(6)
        )
        hsum.append(f'''  have hsum_{coordinate} :
      (∑ k : Fin 30, ((candidateInverseInterval2600 0 k).mul
        (analyticMomentInterval2597 k 0)).{coordinate}) =
      {real_expr(str(sums[coordinate]))} := by
    rw [fin30_sum_eq_six_blocks]
    rw [{blocks}]
    norm_num
''')
    output = DEV / "C1RouteACorrectionStaticDefectSumBlockProbe2600Cell0000.lean"
    output.write_text(f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common
import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 0 in
theorem candidateInverseDefectEntryBound2600_block_probe_00_00 :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 0 0) ≤
      analyticDefectEntryBounds2595 0 0 := by
{''.join(hsum)}  apply NNReal.coe_le_coe.mp
  change
    (max |(matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 0).reLo|
        |(matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 0).reHi| +
      max |(matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 0).imLo|
        |(matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 0).imHi|) ≤
      (analyticDefectEntryBounds2595 0 0 : ℝ)
  rw [matrixDefectInterval2598_reLo, matrixDefectInterval2598_reHi,
    matrixDefectInterval2598_imLo, matrixDefectInterval2598_imHi]
  rw [hsum_reHi, hsum_reLo, hsum_imHi, hsum_imLo]
  norm_num [analyticDefectEntryBounds2595,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end ConnesWeilRH.Dev
''', encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
