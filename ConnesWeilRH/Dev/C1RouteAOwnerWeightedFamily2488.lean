import ConnesWeilRH.Dev.C1RouteALocalBumpFactors2487
import ConnesWeilRH.Dev.C1RouteAOwnerLocalCurvature2475

/-  2488: weighted finite-family composition for the actual owner.

The local bump interface supplies bounds for one family term.  This theorem
keeps the owner as the literal 30-term sum and composes those bounds after the
sigma weight has been applied.  It remains parameterized by family-level
analytic bounds; no table entry is promoted to a proof premise here.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

set_option linter.style.longLine false
set_option maxRecDepth 32768

/- A single-family adapter for the weighted chord estimate.  Keeping the
   three derivative bounds explicit is intentional: the eventual interval
   proof must discharge them from the local bump interface, rather than hide
   them in a precomputed familyBound. -/

theorem weightedExternalFamilySecondDeriv_le_of_local_bounds2488
    (sigma x modulation radius zeroBound firstBound secondBound : ℝ)
    (hcoeff : ℂ)
    (hradius : 0 < radius) (hinside : |x| < radius)
    (hzero : ‖externalFamilyValue2344 hcoeff modulation radius x‖ ≤ zeroBound)
    (hfirst : ‖deriv (externalFamilyValue2344 hcoeff modulation radius) x‖ ≤ firstBound)
    (hsecond : ‖deriv (deriv (externalFamilyValue2344 hcoeff modulation radius)) x‖ ≤
      secondBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 hcoeff modulation radius))) x‖ ≤
      weightedCurvature2348 sigma radius zeroBound firstBound secondBound := by
  have hsmooth : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (externalFamilyValue2344 hcoeff modulation radius) :=
    (externalFamilyValue2344_contDiff hcoeff modulation radius hradius).of_le
      (by decide)
  exact weightedFunction2348_curvature_bound sigma
    (externalFamilyValue2344 hcoeff modulation radius) hsmooth radius x
    zeroBound firstBound secondBound (le_of_lt (abs_lt.mp hinside)) hzero hfirst hsecond

theorem externalFamilyValue2344_secondDerivative_norm_le_of_factor_bounds2488
    (coefficient : ℂ) (modulation radius position : ℝ)
    (valueBound factorBound : ℝ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfactor : ‖familySecondFactor2345 modulation radius position‖ ≤ factorBound) :
    ‖deriv (deriv (externalFamilyValue2344 coefficient modulation radius)) position‖ ≤
      valueBound * factorBound := by
  rw [externalFamilyValue2344_secondDerivative_inside coefficient modulation hradius hinside]
  exact (norm_mul _ _).trans (mul_le_mul hvalue hfactor (norm_nonneg _) (by positivity))

theorem externalFamilyValue2344_firstDerivative_norm_le_of_factor_bounds2488
    (coefficient : ℂ) (modulation radius position : ℝ)
    (valueBound factorBound : ℝ)
    (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfactor : ‖familyFirstFactor2345 modulation radius position‖ ≤ factorBound) :
    ‖deriv (externalFamilyValue2344 coefficient modulation radius) position‖ ≤
      valueBound * factorBound := by
  have hderiv := (externalFamilyValue2344_hasDerivAt_inside
    coefficient modulation hradius hinside).deriv
  rw [hderiv]
  have hinterior :
      familyInterior2345 coefficient modulation radius position =
        externalFamilyValue2344 coefficient modulation radius position := by
    simp only [externalFamilyValue2344, familyInterior2345, familyLog2345,
      familyDeficit2345, if_pos hinside]
  rw [hinterior]
  exact (norm_mul _ _).trans (mul_le_mul hvalue hfactor (norm_nonneg _) (by positivity))

theorem weightedExternalFamilySecondDeriv_le_of_factor_bounds2488
    (sigma position modulation radius valueBound firstFactorBound secondFactorBound : ℝ)
    (coefficient : ℂ) (hradius : 0 < radius) (hinside : |position| < radius)
    (hvalue : ‖externalFamilyValue2344 coefficient modulation radius position‖ ≤ valueBound)
    (hfirstFactor : ‖familyFirstFactor2345 modulation radius position‖ ≤ firstFactorBound)
    (hsecondFactor : ‖familySecondFactor2345 modulation radius position‖ ≤ secondFactorBound) :
    ‖deriv (deriv (weightedFunction2348 sigma
      (externalFamilyValue2344 coefficient modulation radius))) position‖ ≤
      weightedCurvature2348 sigma radius valueBound
        (valueBound * firstFactorBound) (valueBound * secondFactorBound) := by
  apply weightedExternalFamilySecondDeriv_le_of_local_bounds2488 sigma position modulation radius
    valueBound (valueBound * firstFactorBound) (valueBound * secondFactorBound) coefficient
    hradius hinside hvalue
  · exact externalFamilyValue2344_firstDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position valueBound firstFactorBound hradius hinside
      hvalue hfirstFactor
  · exact externalFamilyValue2344_secondDerivative_norm_le_of_factor_bounds2488
      coefficient modulation radius position valueBound secondFactorBound hradius hinside
      hvalue hsecondFactor

theorem ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488
    (sigma x : ℝ) (familyBound : Fin 30 → ℝ)
    (hfamily : ∀ i : Fin 30,
      ‖deriv (deriv (weightedFunction2348 sigma
        (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i)))) x‖ ≤ familyBound i) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ∑ i : Fin 30, familyBound i := by
  let family := fun i : Fin 30 =>
    weightedFunction2348 sigma
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i))
  have hsmooth : ∀ i : Fin 30,
      ContDiff ℝ (2 : WithTop (WithTop ℕ)) (family i) := fun i =>
    weightedFunction2348_contDiff sigma _
      ((externalFamilyValue2344_contDiff _ _ _ (ownerRadPos_2465 i)).of_le
        (by decide))
  have hsmoothAt : ∀ i : Fin 30, ContDiffAt ℝ 2 (family i) x := fun i =>
    (hsmooth i).contDiffAt
  have hsum : ‖iteratedDeriv 2 (fun y => ∑ i : Fin 30, family i y) x‖ ≤
      ∑ i : Fin 30, familyBound i := by
    rw [iteratedDeriv_fun_sum (fun i _ => hsmoothAt i)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hfamily i)
  rw [show weightedFunction2348 sigma ownerPanelSumValue_2467 =
      fun y => ∑ i : Fin 30, family i y by
    funext y
    simp only [weightedFunction2348, ownerPanelSumValue_2467, family]
    exact Finset.mul_sum (Finset.univ : Finset (Fin 30))
      (fun i : Fin 30 => externalFamilyValue2344
        (ownerCoef_2463 i) (ownerMod_2463 i) (ownerRad_2463 i) y)
      (weightedExp2348 sigma y)]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hsum

end ConnesWeilRH.Dev
