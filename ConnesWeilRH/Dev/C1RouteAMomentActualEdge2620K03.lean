import ConnesWeilRH.Dev.C1RouteAMomentScalarEdge2620K03
import ConnesWeilRH.Dev.C1RouteAMomentEdgeBound2619

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem actualMomentEntry03_bothEdgeCharge_le2620 :
    |(storedWidth 3 ^ 2) *
      ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
          realNormalizedMomentIntegrand2618 (storedWidth 3 ^ 2)
            (capturedNodes2584 3).re position) +
        (∫ position in (9 / 10 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth 3 ^ 2)
            (capturedNodes2584 3).re position))| ≤
      (4 : ℝ) / 10 ^ 69 := by
  have hradius : 0 < storedWidth 3 ^ 2 := pow_pos (storedWidth_pos 3) 2
  have hbase := realNormalizedMomentIntegrand2618_edge_integral_bound
    (storedWidth 3 ^ 2) (capturedNodes2584 3).re (9 / 10)
    (by norm_num) (by norm_num)
  have hexp := momentScalarEdge2620K03_error
  have hupper := (abs_le.mp hexp).2
  have hbound : momentEdgeUpper2619 (storedWidth 3 ^ 2)
      (capturedNodes2584 3).re (9 / 10) ≤
      (momentScalarEdge2620K03Expected.1.1 : ℝ) +
        (momentScalarEdge2620K03Expected.2 : ℝ) := by
    unfold momentEdgeUpper2619
    linarith
  rw [abs_mul, abs_of_pos hradius]
  calc
    _ ≤ (storedWidth 3 ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          momentEdgeUpper2619 (storedWidth 3 ^ 2)
            (capturedNodes2584 3).re (9 / 10)) :=
      mul_le_mul_of_nonneg_left hbase hradius.le
    _ ≤ (storedWidth 3 ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          ((momentScalarEdge2620K03Expected.1.1 : ℝ) +
            (momentScalarEdge2620K03Expected.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound (by norm_num)) hradius.le
    _ ≤ _ := by
      norm_num [momentScalarEdge2620K03Expected, storedWidth,
        Matrix.cons_val_three, Matrix.cons_val_zero]

end ConnesWeilRH.Dev
