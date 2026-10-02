import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget2468

/-  2484: finite-family local derivative interface for the actual owner.

This separates the analytic work into two obligations: a future cell proof
supplies one local bound for each of the 30 family terms, and this theorem
composes those bounds without changing the owner or dropping complex norms.
No numerical cell bound is stored here. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

set_option linter.style.longLine false
set_option maxRecDepth 32768

theorem ownerPanelIteratedDeriv_le_sumFamilyBound2484
    (order : ℕ) (x : ℝ)
    (familyBound : Fin 30 → ℝ)
    (hfamily : ∀ i : Fin 30,
      ‖iteratedDeriv order
        (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i)) x‖ ≤ familyBound i) :
    ‖iteratedDeriv order ownerPanelSumValue_2467 x‖ ≤
      ∑ i : Fin 30, familyBound i := by
  let family := fun i : Fin 30 =>
    externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
      (ownerRad_2463 i)
  have hsmooth : ∀ i : Fin 30,
      ContDiff ℝ (∞ : WithTop (WithTop ℕ)) (family i) := fun i =>
    externalFamilyValue2344_contDiff _ _ _ (ownerRadPos_2465 i)
  have hsmoothAt : ∀ i : Fin 30, ContDiffAt ℝ order (family i) x := fun i =>
    ((hsmooth i).of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  rw [show ownerPanelSumValue_2467 = fun y => ∑ i : Fin 30, family i y by
    funext y; rfl]
  rw [iteratedDeriv_fun_sum (fun i _ => hsmoothAt i)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hfamily i)

end ConnesWeilRH.Dev
