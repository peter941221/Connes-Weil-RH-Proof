import ConnesWeilRH.Dev.C1RouteBSourceCellEnvelope2834

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

theorem routeBSourceCharge_sum_le_envelope3020
    {n : ℕ} (S : Finset ℕ) (order : ℕ)
    (hS : ∀ i ∈ S, i < n)
    (envelope : ℕ → ℝ)
    (henvelope : ∀ i ∈ S,
      routeBSourceNorm2834 i order ≤ envelope i) :
    (∑ i ∈ S, routeBSourceCharge2834 i order) ≤
      ∑ i ∈ S, 4 * ((2047 : ℝ) / 33554432) * envelope i := by
  apply Finset.sum_le_sum
  intro i hi
  rw [routeBSourceCharge_eq_width_norm2834]
  have hw : 0 ≤ 4 * ((2047 : ℝ) / 33554432) := by positivity
  exact mul_le_mul_of_nonneg_left (henvelope i hi) hw

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
