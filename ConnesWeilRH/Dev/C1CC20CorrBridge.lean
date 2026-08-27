/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20LpOperatorNorm

/-!
# The CC20 correlation-slice bridge (engine of paper eq. (121))

First half of the Lemma-3 engine of arXiv:2006.13771: Cauchy--Schwarz on a
displacement slice, UNIFORM in the displacement parameter,

    ‖corrInnerSlice η ξ v‖ ≤ mass(η)^(1/2) · mass(shift_v ξ)^(1/2).

The paper's Hermitian conjugation on the first factor belongs to the
consumption site and is deliberately not inserted here: the bound is proved
for arbitrary complex factors, so feeding a conjugated first argument at
the call site reproduces (121) verbatim.

Translation enters through one explicit premise slot, to be discharged once
and forever by the forthcoming translation-invariance leaf:

* `hxiShiftedMemLp` — shifting preserves `MemLp 2`.

The remaining half of the engine — folding the uniform bound over `v`
against an integrable weight into the full pairing domination
(paper (121)) — is contracted in docs 1043 §6n as brick L2b and needs,
besides this theorem, the shift-invariance of the real squared-norm mass
plus integrability bookkeeping for the weight.

No RH-level sign or coverage claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20CorrBridge

open MeasureTheory

/-- The inner displacement slice at parameter `v`: correlation of `η`
against the translate `x ↦ ξ(x+v)`. -/
noncomputable def corrInnerSlice (η ξ : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ x : ℝ, η x * ξ (x + v)

/-- Uniform Cauchy--Schwarz on slices.  For every displacement `v`,
the slice value is dominated by the product of the square roots of the two
real squared-norm masses — exactly the pointwise inequality the paper folds
over `v` against an `L¹` weight in its equation (121). -/
theorem abs_corrInnerSlice_le
    {η ξ : ℝ → ℂ}
    (heta : MemLp η (ENNReal.ofReal 2))
    (hxiShiftedMemLp : ∀ w : ℝ, MemLp (fun x => ξ (x + w)) (ENNReal.ofReal 2))
    (v : ℝ) :
    ‖corrInnerSlice η ξ v‖ ≤
      (∫ x, ‖η x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖ξ (x + v)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  -- Cauchy--Schwarz, verbatim instantiation of the proven LpOperator pattern
  -- with the row replaced by the translated slice family.
  have hraw :
      (∫ x, ‖η x‖ * ‖ξ (x + v)‖) ≤
        (∫ x, ‖η x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖ξ (x + v)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hholder heta
      (hxiShiftedMemLp v)
  calc
    ‖corrInnerSlice η ξ v‖ ≤ ∫ x, ‖η x * ξ (x + v)‖ :=
      by
        rw [corrInnerSlice]
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x, ‖η x‖ * ‖ξ (x + v)‖ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul]
    _ ≤ (∫ x, ‖η x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖ξ (x + v)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hraw

end C1CC20CorrBridge
end Source
end ConnesWeilRH
