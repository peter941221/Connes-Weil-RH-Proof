import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget2468

/-  2479: align the MPFR smoke's conservative coefficient binding with Lean.

The numerical preflight bounds each complex owner coefficient by
`|re c| + |im c|`.  This file records that this is a genuine upper bound for
the existing 2350 derivative budget, and transports the 2468 owner derivative
bound through it.  It is an interface lemma only: it does not import a
floating-point result or assert a producer certificate. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

set_option linter.style.longLine false
set_option maxRecDepth 32768

noncomputable def familyDerivativeBudgetL1_2479 (order : ℕ) (coefficient : ℂ)
    (modulation radius : ℝ) : ℝ :=
  (|coefficient.re| + |coefficient.im|) * ∑ index ∈ Finset.range (order + 1),
    (order.choose index : ℝ) * |modulation| ^ index *
      ((bumpConstant2350 (order - index) : ℝ) * Real.exp (-30) /
        radius ^ (order - index))

theorem familyDerivativeBudget2350_le_l1_2479 (order : ℕ) (coefficient : ℂ)
    (modulation radius : ℝ) (hradius : 0 < radius) :
    familyDerivativeBudget2350 order coefficient modulation radius ≤
      familyDerivativeBudgetL1_2479 order coefficient modulation radius := by
  unfold familyDerivativeBudget2350 familyDerivativeBudgetL1_2479
  apply mul_le_mul_of_nonneg_right
  · exact Complex.norm_le_abs_re_add_abs_im coefficient
  · apply Finset.sum_nonneg
    intro index hindex
    positivity

noncomputable def ownerDerivativeBudgetL1_2479 (order : ℕ) : ℝ :=
  ∑ i : Fin 30,
    familyDerivativeBudgetL1_2479 order (ownerCoef_2463 i) (ownerMod_2463 i)
      (ownerRad_2463 i)

theorem ownerDerivativeBudget_2468_le_l1_2479 (order : ℕ) :
    ownerDerivativeBudget_2468 order ≤ ownerDerivativeBudgetL1_2479 order := by
  unfold ownerDerivativeBudget_2468 ownerDerivativeBudgetL1_2479
  exact Finset.sum_le_sum fun i _ =>
    familyDerivativeBudget2350_le_l1_2479 order (ownerCoef_2463 i)
      (ownerMod_2463 i) (ownerRad_2463 i) (ownerRadPos_2465 i)

theorem ownerPanelIteratedDerivBudgetL1_2479 (order : ℕ) (horder : order ≤ 4)
    (x : ℝ) :
    ‖iteratedDeriv order (ownerPanelSumValue_2467) x‖ ≤
      ownerDerivativeBudgetL1_2479 order := by
  exact (ownerPanelIteratedDerivBudget_2468 order horder x).trans
    (ownerDerivativeBudget_2468_le_l1_2479 order)

end ConnesWeilRH.Dev
