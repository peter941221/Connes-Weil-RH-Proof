import ConnesWeilRH.Dev.C1RouteAExpCurvatureUpper2509

/-! Record 2510: single-family second-derivative consumer.

This theorem is the direct hcell-facing interface: factor bounds establish the
exact curvature slots, while one certified exponential upper replaces all
three slots through record 2509.
-/

namespace ConnesWeilRH.Dev

theorem weightedExternalFamilySecondDeriv_le_of_exp_upper_factor_bounds2510
    (sigma position modulation radius c p1 p2 x upper : ℝ)
    (coefficient : ℂ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hc : 0 ≤ c) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤
      c * Real.exp (-x))
    (hfirst : ‖familyFirstFactor2345 modulation radius position‖ ≤ p1)
    (hsecond : ‖familySecondFactor2345 modulation radius position‖ ≤ p2)
    (hexp : Real.exp (-x) ≤ upper) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius
        (c * upper) (c * upper * p1) (c * upper * p2) := by
  have hbase := weightedExternalFamilySecondDeriv_le_of_factor_bounds2488
    sigma position modulation radius
      (c * Real.exp (-x))
      p1 p2
      coefficient hradius hinside hvalue hfirst hsecond
  exact hbase.trans (weightedCurvature2348_mono_exp_upper2509
    sigma radius c p1 p2 x upper hc hp1 hp2 hexp)

end ConnesWeilRH.Dev
