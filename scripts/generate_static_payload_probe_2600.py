"""Generate a static-coordinate consumer probe for Row00/Col00."""

import json
from fractions import Fraction

from generate_static_defect_bounds_2600 import DEV, WITNESS, real_expr
from generate_static_sum_block_probe_2600 import product_coords


def main() -> None:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    sums = {
        coordinate: sum(
            (product_coords(inverse[0][inner], matrix[inner][0])[coordinate]
             for inner in range(30)),
            Fraction(0),
        )
        for coordinate in ("reLo", "reHi", "imLo", "imHi")
    }
    defect = {
        "reLo": Fraction(1) - sums["reHi"],
        "reHi": Fraction(1) - sums["reLo"],
        "imLo": -sums["imHi"],
        "imHi": -sums["imLo"],
    }
    sum_haves = []
    for coordinate in ("reLo", "reHi", "imLo", "imHi"):
        blocks = ", ".join(
            f"candidateInverseAnalyticSumBlock2600_00_00_{block}_{coordinate}"
            for block in range(6)
        )
        sum_haves.append(f'''  have hsum_{coordinate} :
      (∑ k : Fin 30, ((candidateInverseInterval2600 0 k).mul
        (analyticMomentInterval2597 k 0)).{coordinate}) =
      {real_expr(str(sums[coordinate]))} := by
    rw [fin30_sum_eq_six_blocks]
    rw [{blocks}]
    norm_num
''')
    static_fields = ",\n  ".join(
        f"{coordinate} := {real_expr(str(defect[coordinate]))}"
        for coordinate in ("reLo", "reHi", "imLo", "imHi")
    )
    output = DEV / "C1RouteACorrectionStaticDefectPayloadProbe2600Cell0000.lean"
    output.write_text(f'''import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common
import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00

namespace ConnesWeilRH.Dev

noncomputable def staticDefectInterval2600_00_00 : ComplexRect2427 :=
  {{ {static_fields} }}

set_option maxHeartbeats 0 in
theorem matrixDefectInterval2600_00_00_eq_static :
    matrixDefectInterval2598 candidateInverseInterval2600 analyticMomentInterval2597 0 0 =
      staticDefectInterval2600_00_00 := by
{''.join(sum_haves)}  apply ComplexRect2427.ext
  · rw [matrixDefectInterval2598_reLo, hsum_reHi]
    norm_num [staticDefectInterval2600_00_00]
  · rw [matrixDefectInterval2598_reHi, hsum_reLo]
    norm_num [staticDefectInterval2600_00_00]
  · rw [matrixDefectInterval2598_imLo, hsum_imHi]
    norm_num [staticDefectInterval2600_00_00]
  · rw [matrixDefectInterval2598_imHi, hsum_imLo]
    norm_num [staticDefectInterval2600_00_00]

set_option maxHeartbeats 0 in
theorem candidateInverseDefectEntryBound2600_static_payload_probe_00_00 :
    rectL1Upper2598 (matrixDefectInterval2598
      candidateInverseInterval2600 analyticMomentInterval2597 0 0) ≤
      analyticDefectEntryBounds2595 0 0 := by
  rw [matrixDefectInterval2600_00_00_eq_static]
  norm_num [rectL1Upper2598, staticDefectInterval2600_00_00,
    analyticDefectEntryBounds2595, Matrix.cons_val_zero, Matrix.cons_val_one]

end ConnesWeilRH.Dev
''', encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
