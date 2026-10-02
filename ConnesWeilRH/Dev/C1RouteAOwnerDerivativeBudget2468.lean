import ConnesWeilRH.Dev.C1RouteAOwnerPanelNormBridge2467
import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget

/-  2468: derivative-budget attachment for the actual indexed owner.

The 2350 single-family budget is reused with the exact 2460 owner radius,
coefficient, and modulation arrays.  The finite-family derivative is then
bounded by the sum of those per-family budgets.  This supplies the actual
second-derivative side needed by the 2457 ζ interface, without importing the
older storedWidth owner as a substitute. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

set_option linter.style.longLine false
set_option maxRecDepth 32768

noncomputable def ownerDerivativeBudget_2468 (order : ℕ) : ℝ :=
  ∑ i : Fin 30,
    familyDerivativeBudget2350 order (ownerCoef_2463 i) (ownerMod_2463 i)
      (ownerRad_2463 i)

theorem ownerPanelIteratedDerivBudget_2468 (order : ℕ) (horder : order ≤ 4)
    (x : ℝ) :
    ‖iteratedDeriv order (ownerPanelSumValue_2467) x‖ ≤
      ownerDerivativeBudget_2468 order := by
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
  unfold ownerDerivativeBudget_2468
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    externalFamilyValue2344_iteratedDeriv_budget2350 order horder
      (ownerCoef_2463 i) (ownerMod_2463 i)
      (radius := ownerRad_2463 i) (position := x)
      (ownerRadPos_2465 i))

theorem ownerPanelSecondDerivBudget_2468 (x : ℝ) :
    ‖deriv (deriv ownerPanelSumValue_2467) x‖ ≤
      ownerDerivativeBudget_2468 2 := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    ownerPanelIteratedDerivBudget_2468 2 (by decide) x

end ConnesWeilRH.Dev
