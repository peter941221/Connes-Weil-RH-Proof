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
