import ConnesWeilRH.Dev.C1RouteAExpFamilySecondDerivUpper2510

/-! Record 2511: sum the certified exponential family uppers.

This is the panel-level hcell interface.  It keeps the family data explicit,
so no stored numerical table is silently promoted to a proof.
-/

namespace ConnesWeilRH.Dev

theorem ownerPanelWeightedSecondDeriv_le_sumExpUpper2511
    (sigma x : ℝ)
    (c p1 p2 exponent upper : Fin 30 → ℝ)
    (hdata : ∀ i : Fin 30,
      0 ≤ c i ∧ 0 ≤ p1 i ∧ 0 ≤ p2 i ∧
      ‖externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i) x‖ ≤ c i * Real.exp (-(exponent i)) ∧
      ‖familyFirstFactor2345 (ownerMod_2463 i) (ownerRad_2463 i) x‖ ≤ p1 i ∧
      ‖familySecondFactor2345 (ownerMod_2463 i) (ownerRad_2463 i) x‖ ≤ p2 i ∧
      Real.exp (-(exponent i)) ≤ upper i)
    (hinside : ∀ i : Fin 30, |x| < ownerRad_2463 i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, weightedCurvature2348 sigma (ownerRad_2463 i)
        (c i * upper i) (c i * upper i * p1 i)
        (c i * upper i * p2 i) := by
  apply ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
  intro i
  rcases hdata i with ⟨hc, hp1, hp2, hvalue, hfirst, hsecond, hexp⟩
  exact weightedExternalFamilySecondDeriv_le_of_exp_upper_factor_bounds2510
    sigma x (ownerMod_2463 i) (ownerRad_2463 i)
    (c i) (p1 i) (p2 i) (exponent i) (upper i)
    (ownerCoef_2463 i) (ownerRadPos_2465 i) (hinside i)
    hc hp1 hp2 hvalue hfirst hsecond hexp

end ConnesWeilRH.Dev
