import ConnesWeilRH.Dev.C1RouteAWeightedCurvatureMonotone2499

/-! Record 2509: propagate one exponential upper bound through curvature slots.

The cell proof supplies one bound for the bump exponential.  This lemma
packages its monotone propagation into the zero, first-derivative, and
second-derivative inputs of `weightedCurvature2348`.
-/

namespace ConnesWeilRH.Dev

theorem weightedCurvature2348_mono_exp_upper2509
    (sigma radius c p1 p2 x upper : ℝ)
    (hc : 0 ≤ c) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hexp : Real.exp (-x) ≤ upper) :
    weightedCurvature2348 sigma radius
        (c * Real.exp (-x))
        (c * Real.exp (-x) * p1)
        (c * Real.exp (-x) * p2) ≤
      weightedCurvature2348 sigma radius
        (c * upper)
        (c * upper * p1)
        (c * upper * p2) := by
  have hzero : c * Real.exp (-x) ≤ c * upper := by
    exact mul_le_mul_of_nonneg_left hexp hc
  have hfirst : c * Real.exp (-x) * p1 ≤ c * upper * p1 := by
    exact mul_le_mul_of_nonneg_right hzero hp1
  have hsecond : c * Real.exp (-x) * p2 ≤ c * upper * p2 := by
    exact mul_le_mul_of_nonneg_right hzero hp2
  exact weightedCurvature2348_mono_bounds2499
    sigma radius _ _ _ _ _ _ hzero hfirst hsecond

end ConnesWeilRH.Dev
