/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaBessel

/-!
# Contractivity-only obstruction for the weighted Julia range row

The normalized Schur transfer is contractive, but that fact alone does not
produce the weighted range-sine estimate.  This file gives an exact scalar
guard: a contractive transfer and a nonzero readout can have a canonical
Julia defect whose energy is strictly smaller than the proposed weighted row.

This is deliberately an abstract contractivity guard.  It is not a model of
the CCM24 graph sine and it does not assert a source-specific obstruction.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaRangeSineContractivityObstruction

open CCM24FiniteSJuliaBessel

local notation "ScalarOp" => ℂ →L[ℂ] ℂ

noncomputable def guardTransfer : ScalarOp :=
  ((79 / 101 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ

noncomputable def guardRangeSine : ScalarOp :=
  ((20 / 101 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ

noncomputable def guardWeight : ℝ := 9401 / 400

theorem guardTransfer_norm_le_one : ‖guardTransfer‖ ≤ 1 := by
  rw [guardTransfer, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    ContinuousLinearMap.norm_id]
  norm_num

theorem guardTransfer_contract :
    ContinuousLinearMap.adjoint guardTransfer ∘L guardTransfer ≤
      ContinuousLinearMap.id ℂ ℂ := by
  exact adjoint_comp_self_le_id_of_norm_le_one guardTransfer
    guardTransfer_norm_le_one

theorem guardTransfer_apply_one_normSq :
    ‖guardTransfer (1 : ℂ)‖ ^ 2 = (79 / 101 : ℝ) ^ 2 := by
  simp only [guardTransfer, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  norm_num

theorem guardRangeSine_apply_one_normSq :
    ‖guardRangeSine (1 : ℂ)‖ ^ 2 = (20 / 101 : ℝ) ^ 2 := by
  simp only [guardRangeSine, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  norm_num

theorem guardCanonicalDefect_apply_one_normSq :
    ‖canonicalJuliaDefect guardTransfer guardTransfer_contract (1 : ℂ)‖ ^ 2 =
      (3960 / 10201 : ℝ) := by
  have hpyth := canonicalJuliaDefect_pythagorean guardTransfer
    guardTransfer_contract (1 : ℂ)
  rw [guardTransfer_apply_one_normSq] at hpyth
  norm_num at hpyth ⊢
  linarith

theorem guardWeightedRangeSine_apply_one_normSq :
    guardWeight * ‖guardRangeSine (1 : ℂ)‖ ^ 2 =
      (9401 / 10201 : ℝ) := by
  rw [guardRangeSine_apply_one_normSq]
  norm_num [guardWeight]

theorem no_contractivity_only_weighted_range_sine_estimate :
    ¬ (∀ x : ℂ,
      guardWeight * ‖guardRangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect guardTransfer guardTransfer_contract x‖ ^ 2) := by
  intro hestimate
  have hpoint := hestimate (1 : ℂ)
  rw [guardWeightedRangeSine_apply_one_normSq,
    guardCanonicalDefect_apply_one_normSq] at hpoint
  norm_num at hpoint

end CCM24FiniteSActualJuliaRangeSineContractivityObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
