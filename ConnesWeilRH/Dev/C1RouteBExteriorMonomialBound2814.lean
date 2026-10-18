import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_monomial_bound2814
    {C T x : ℝ} {q : ℕ}
    (hC : 0 ≤ C) (hT : 0 < T) (hx : T ≤ x) :
    C * x⁻¹ ^ q ≤ C * T⁻¹ ^ q := by
  have hxi : 0 ≤ x⁻¹ := le_of_lt (inv_pos.mpr (lt_of_lt_of_le hT hx))
  have hTi : 0 ≤ T⁻¹ := le_of_lt (inv_pos.mpr hT)
  have hinv : x⁻¹ ≤ T⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hT hx)
  have hp : x⁻¹ ^ q ≤ T⁻¹ ^ q := pow_le_pow_left₀ hxi hinv q
  exact mul_le_mul_of_nonneg_left hp hC

theorem routeB_exterior_monomial_scaled_bound2814
    {C T x scale : ℝ} {q : ℕ}
    (hC : 0 ≤ C) (hscale : 0 ≤ scale) (hT : 0 < T) (hx : T ≤ x) :
    C * scale * x⁻¹ ^ q ≤ C * scale * T⁻¹ ^ q := by
  have h := routeB_exterior_monomial_bound2814
    (C := C * scale) (T := T) (x := x) (q := q)
    (mul_nonneg hC hscale) hT hx
  simpa [mul_assoc] using h

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
