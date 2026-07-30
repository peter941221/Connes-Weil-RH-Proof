/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

/-!
# Quotient guard for bone 1

Proofs 575--579 identify the missing source obligation as a bounded quotient:
the signed raw row must factor through the packed physical analysis with one
common norm bound.  This file records a sharp logical guard for that step.

Injectivity of each analysis map, positivity of its Gram operator, and a
uniform operator-norm bound for the raw row do not imply a uniform Douglas
constant.  The scalar family below has analysis `A_epsilon = epsilon I` and
raw row `R = I`.  Every individual analysis is injective and positive, but
the family has arbitrarily small analysis energy while the raw output at `1`
stays equal to one.

This is an abstract countermodel only.  It is not a claim that the actual
finite-S CCM24 carrier contains this family.  The source-specific task remains
to prove the real signed quotient estimate, or to construct the corresponding
approximate kernel on the real carrier.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierQuotientGuard

local notation "ScalarOp" => ℂ →L[ℂ] ℂ

/-! ## The scalar family -/

noncomputable def guardAnalysis (epsilon : ℝ) : ScalarOp :=
  (epsilon : ℂ) • ContinuousLinearMap.id ℂ ℂ

noncomputable def guardRaw : ScalarOp :=
  ContinuousLinearMap.id ℂ ℂ

theorem guardRaw_norm_le_one : ‖guardRaw‖ ≤ (1 : ℝ) := by
  simp [guardRaw]

theorem guardAnalysis_norm_le_one_of_unit_interval
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    ‖guardAnalysis epsilon‖ ≤ (1 : ℝ) := by
  rw [guardAnalysis, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    ContinuousLinearMap.norm_id]
  rw [abs_of_nonneg hepsilon]
  simpa using hone

theorem guardAnalysis_apply_one_normSq (epsilon : ℝ) :
    ‖guardAnalysis epsilon (1 : ℂ)‖ ^ 2 = epsilon ^ 2 := by
  rw [guardAnalysis]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_one]
  simpa only [mul_one] using (sq_abs epsilon)

theorem guardRaw_apply_one_normSq :
    ‖guardRaw (1 : ℂ)‖ ^ 2 = (1 : ℝ) := by
  simp [guardRaw]

theorem guardAnalysis_injective
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    Function.Injective (guardAnalysis epsilon) := by
  intro x y hxy
  have hzero : guardAnalysis epsilon (x - y) = 0 := by
    rw [map_sub, hxy]
    simp
  have hmul : (epsilon : ℂ) * (x - y) = 0 := by
    simpa [guardAnalysis, smul_eq_mul] using hzero
  have hdiff : x - y = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left
      (Complex.ofReal_ne_zero.mpr hepsilon)
  exact sub_eq_zero.mp hdiff

theorem guardAnalysis_gram_isPositive (epsilon : ℝ) :
    ((ContinuousLinearMap.adjoint (guardAnalysis epsilon)) ∘L
      guardAnalysis epsilon).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-! ## Failure of a family-uniform Douglas bound -/

theorem no_uniform_scalar_douglas :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ x : ℂ,
          ‖guardRaw x‖ ^ 2 ≤
            C ^ 2 * ‖guardAnalysis epsilon x‖ ^ 2 := by
  rintro ⟨C, _hC, hbound⟩
  let epsilon : ℝ := 1 / (|C| + 1)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hpoint := hbound epsilon hepsilon (1 : ℂ)
  rw [guardRaw_apply_one_normSq, guardAnalysis_apply_one_normSq] at hpoint
  have hsquare : C ^ 2 < (|C| + 1) ^ 2 := by
    rw [← sq_abs C]
    nlinarith [abs_nonneg C]
  have hden : 0 < (|C| + 1) ^ 2 := by
    positivity
  have hratio : C ^ 2 / (|C| + 1) ^ 2 < (1 : ℝ) := by
    apply (div_lt_iff₀ hden).2
    simpa using hsquare
  have hstrict : C ^ 2 * epsilon ^ 2 < (1 : ℝ) := by
    dsimp [epsilon]
    calc
      C ^ 2 * (1 / (|C| + 1)) ^ 2 =
          C ^ 2 / (|C| + 1) ^ 2 := by
            simp [div_pow]
            simpa only [div_eq_mul_inv]
      _ < 1 := hratio
  exact (not_lt_of_ge hpoint) hstrict

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierQuotientGuard
end CCM25Concrete
end Source
end ConnesWeilRH
