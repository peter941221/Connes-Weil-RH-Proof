import ConnesWeilRH.Dev.C1RouteBExteriorMonomialBound2814
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open scoped Interval

theorem routeB_exterior_tail_integral_bound2815
    {f : ℝ → ℝ} {C T R : ℝ} {q : ℕ}
    (hC : 0 ≤ C) (hT : 0 < T) (hTR : T ≤ R)
    (hbound : ∀ x ∈ Set.uIoc T R, ‖f x‖ ≤ C * T⁻¹ ^ q) :
    ‖∫ x in T..R, f x‖ ≤ (R - T) * (C * T⁻¹ ^ q) := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := T) (b := R) (C := C * T⁻¹ ^ q) (by
      intro x hx
      exact hbound x hx)
  have hwidth : |R - T| = R - T := abs_of_nonneg (sub_nonneg.mpr hTR)
  rw [hwidth] at hnorm
  simpa [mul_comm] using hnorm

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
