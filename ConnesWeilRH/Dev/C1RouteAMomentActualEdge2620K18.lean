import ConnesWeilRH.Dev.C1RouteAMomentScalarEdge2620K18
import ConnesWeilRH.Dev.C1RouteAMomentEdgeBound2619
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem actualMomentEntry18_bothEdgeCharge_le2620 :
    |(storedWidth 18 ^ 2) *
      ((∫ position in (-1 : ℝ)..(-(9 / 10 : ℝ)),
          realNormalizedMomentIntegrand2618 (storedWidth 18 ^ 2)
            (capturedNodes2584 18).re position) +
        (∫ position in (9 / 10 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth 18 ^ 2)
            (capturedNodes2584 18).re position))| ≤
      (8 : ℝ) / 10 ^ 69 := by
  have hradius : 0 < storedWidth 18 ^ 2 := pow_pos (storedWidth_pos 18) 2
  have hbase := realNormalizedMomentIntegrand2618_edge_integral_bound
    (storedWidth 18 ^ 2) (capturedNodes2584 18).re (9 / 10)
    (by norm_num) (by norm_num)
  have hexp := momentScalarEdge2620K18_error
  have hupper := (abs_le.mp hexp).2
  have hbound : momentEdgeUpper2619 (storedWidth 18 ^ 2)
      (capturedNodes2584 18).re (9 / 10) ≤
      (momentScalarEdge2620K18Expected.1.1 : ℝ) +
        (momentScalarEdge2620K18Expected.2 : ℝ) := by
    unfold momentEdgeUpper2619
    linarith
  rw [abs_mul, abs_of_pos hradius]
  calc
    _ ≤ (storedWidth 18 ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          momentEdgeUpper2619 (storedWidth 18 ^ 2)
            (capturedNodes2584 18).re (9 / 10)) :=
      mul_le_mul_of_nonneg_left hbase hradius.le
    _ ≤ (storedWidth 18 ^ 2) *
        (2 * (1 - (9 / 10 : ℝ)) *
          ((momentScalarEdge2620K18Expected.1.1 : ℝ) +
            (momentScalarEdge2620K18Expected.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbound (by norm_num)) hradius.le
    _ ≤ _ := by
      norm_num [momentScalarEdge2620K18Expected, storedWidth,
        Matrix.cons_val_18, Matrix.cons_val_zero]

end ConnesWeilRH.Dev
