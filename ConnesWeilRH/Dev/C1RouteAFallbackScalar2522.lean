import ConnesWeilRH.Dev.C1RouteAExpFamilyFallback2521

/-! Exact scalar form for the repaired fallback at both producer signs.
The exponential includes the bump's exp(-30), avoiding a coarse independent
upper for exp(radius/2). Numeric leaves must still prove their rational bounds.
-/

namespace ConnesWeilRH.Dev

noncomputable def familyFallbackFactor2522 (coefficient : ℂ) (modulation radius : ℝ) : ℝ :=
  (|coefficient.re| + |coefficient.im|) *
    (3720 / radius ^ 2 + 120 * |modulation| / radius + |modulation| ^ 2 +
      60 / radius + |modulation| + 1 / 4)

theorem familyFallback_scalar2522 (sigma : ℝ) (coefficient : ℂ)
    (modulation radius : ℝ)
    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ)) :
    weightedCurvature2348 sigma radius
      (familyDerivativeBudgetL1_2479 0 coefficient modulation radius)
      (familyDerivativeBudgetL1_2479 1 coefficient modulation radius)
      (familyDerivativeBudgetL1_2479 2 coefficient modulation radius) =
    Real.exp (radius / 2 - 30) * familyFallbackFactor2522 coefficient modulation radius := by
  rw [show radius / 2 - 30 = radius / 2 + (-30) by ring, Real.exp_add]
  rcases hsigma with rfl | rfl <;>
    norm_num [weightedCurvature2348, familyDerivativeBudgetL1_2479,
      familyFallbackFactor2522, Finset.sum_range_succ, bumpConstant2350] <;> ring

theorem ownerFamilyFallback_scalar2522 (sigma : ℝ) (i : Fin 30)
    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ)) :
    ownerFamilyWeightedCurvatureL1_2488 sigma i =
      Real.exp (ownerRad_2463 i / 2 - 30) *
        familyFallbackFactor2522 (ownerCoef_2463 i) (ownerMod_2463 i) (ownerRad_2463 i) :=
  familyFallback_scalar2522 sigma _ _ _ hsigma

end ConnesWeilRH.Dev
