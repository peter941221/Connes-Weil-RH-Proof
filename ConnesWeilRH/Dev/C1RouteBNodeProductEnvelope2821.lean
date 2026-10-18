import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_node_product_envelope2821
    {a b A B : ℝ}
    (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
