/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel

/-!
# The CC20 residue-augmented regular operator

CC20's quantized differential contributes a diagonal `-2 Id` term in addition
to the ordinary finite-window regular kernel.  This module keeps that residue
explicit on the restricted logarithmic carrier and transports the same owner
to the global logarithmic carrier as `K_window - 2 P_window`.

This is the ordinary CC20 remainder owner.  It does not identify that owner
with a finite-`S` post-`Q` semilocal remainder or prove its route sign.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set
open scoped InnerProductSpace

/-- The CC20 regular kernel together with its `-2 Id` diagonal residue on the
finite logarithmic window. -/
noncomputable def cc20GlobalLogWindowRestrictedQuantizedRemainder
    (lambda : ℝ) (hlambda : 1 < lambda) :
    Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
      Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) :=
  cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda -
    (2 : ℂ) • ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)))

theorem cc20GlobalLogWindowRestrictedQuantizedRemainder_apply
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) :
    cc20GlobalLogWindowRestrictedQuantizedRemainder lambda hlambda u =
      cc20GlobalLogWindowRestrictedL2Endomorphism lambda hlambda u -
        (2 : ℂ) • u := by
  simp [cc20GlobalLogWindowRestrictedQuantizedRemainder]

theorem cc20GlobalLogWindowRestrictedQuantizedRemainder_inner_re
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) :
    (⟪u, cc20GlobalLogWindowRestrictedQuantizedRemainder
      lambda hlambda u⟫_ℂ).re =
        (⟪u, cc20GlobalLogWindowRestrictedL2Endomorphism
          lambda hlambda u⟫_ℂ).re - 2 * ‖u‖ ^ 2 := by
  rw [cc20GlobalLogWindowRestrictedQuantizedRemainder_apply,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem cc20GlobalLogWindowRestrictedQuantizedRemainder_isSelfAdjoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsSelfAdjoint
      (cc20GlobalLogWindowRestrictedQuantizedRemainder lambda hlambda) := by
  unfold cc20GlobalLogWindowRestrictedQuantizedRemainder
  apply IsSelfAdjoint.sub
  · exact cc20GlobalLogWindowRestrictedL2Endomorphism_isSelfAdjoint
      lambda hlambda
  · change IsSelfAdjoint
      ((2 : ℂ) •
        (1 : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda)) →L[ℂ]
          Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))))
    exact (IsSelfAdjoint.ofNat 2).smul (IsSelfAdjoint.one _)

/-- The same residue-augmented owner on the whole logarithmic line.  The
identity on the finite window becomes its orthogonal window projection after
zero extension. -/
noncomputable def cc20GlobalLogWindowQuantizedRemainder
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogL2 →L[ℂ] cc20GlobalLogL2 :=
  cc20GlobalLogWindowL2Operator lambda hlambda -
    (2 : ℂ) • cc20LogWindowProjection lambda hlambda

theorem cc20GlobalLogWindowQuantizedRemainder_apply
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2) :
    cc20GlobalLogWindowQuantizedRemainder lambda hlambda u =
      cc20GlobalLogWindowL2Operator lambda hlambda u -
        (2 : ℂ) • cc20LogWindowProjection lambda hlambda u := by
  simp [cc20GlobalLogWindowQuantizedRemainder]

/-- The global `K_window - 2 P_window` owner is exactly zero-extension
conjugation of the restricted `K_I - 2 Id` owner. -/
theorem cc20GlobalLogWindowQuantizedRemainder_eq_zeroExtension_conjugation
    (lambda : ℝ) (hlambda : 1 < lambda) :
    cc20GlobalLogWindowQuantizedRemainder lambda hlambda =
      ((cc20LogWindowRestrictIndicatorCLM lambda).comp
        (cc20GlobalLogWindowRestrictedQuantizedRemainder
          lambda hlambda)).comp
            (cc20LogWindowRestrictIndicatorCLM lambda).adjoint := by
  apply ContinuousLinearMap.ext
  intro u
  rw [cc20GlobalLogWindowQuantizedRemainder_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [cc20GlobalLogWindowRestrictedQuantizedRemainder_apply,
    cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation,
    ← cc20LogWindowRestrictIndicator_comp_restrict lambda hlambda,
    cc20LogWindowRestrict_eq_adjoint_restrictIndicatorCLM]
  simp only [ContinuousLinearMap.comp_apply, map_sub, map_smul]

theorem cc20GlobalLogWindowQuantizedRemainder_isSelfAdjoint
    (lambda : ℝ) (hlambda : 1 < lambda) :
    IsSelfAdjoint (cc20GlobalLogWindowQuantizedRemainder lambda hlambda) := by
  rw [cc20GlobalLogWindowQuantizedRemainder_eq_zeroExtension_conjugation]
  exact
    (cc20GlobalLogWindowRestrictedQuantizedRemainder_isSelfAdjoint
      lambda hlambda).conj_adjoint
        (cc20LogWindowRestrictIndicatorCLM lambda)

/-- The global and restricted residue-augmented quadratic forms agree on the
zero-extension range.  This is the same-carrier bridge for the complete
`K_I - 2 Id` owner, not only for its compact regular part. -/
theorem cc20GlobalLogWindowQuantizedRemainder_inner_zeroExtension
    (lambda : ℝ) (hlambda : 1 < lambda)
    (u : Lp ℂ 2 (volume.restrict (cc20LogWindow lambda))) :
    inner ℂ (cc20LogWindowRestrictIndicatorCLM lambda u)
        (cc20GlobalLogWindowQuantizedRemainder lambda hlambda
          (cc20LogWindowRestrictIndicatorCLM lambda u)) =
      inner ℂ u
        (cc20GlobalLogWindowRestrictedQuantizedRemainder
          lambda hlambda u) := by
  calc
    inner ℂ (cc20LogWindowRestrictIndicatorCLM lambda u)
        (cc20GlobalLogWindowQuantizedRemainder lambda hlambda
          (cc20LogWindowRestrictIndicatorCLM lambda u)) =
        inner ℂ (cc20LogWindowRestrictIndicatorCLM lambda u)
          (cc20LogWindowRestrictIndicatorCLM lambda
            (cc20GlobalLogWindowRestrictedQuantizedRemainder
              lambda hlambda u)) := by
      rw [cc20GlobalLogWindowQuantizedRemainder_eq_zeroExtension_conjugation]
      simp only [ContinuousLinearMap.comp_apply]
      rw [← cc20LogWindowRestrict_eq_adjoint_restrictIndicatorCLM,
        cc20LogWindowRestrict_restrictIndicator]
    _ = inner ℂ u
        (cc20GlobalLogWindowRestrictedQuantizedRemainder
          lambda hlambda u) := by
      rw [← ContinuousLinearMap.adjoint_inner_right
        (cc20LogWindowRestrictIndicatorCLM lambda)]
      rw [← cc20LogWindowRestrict_eq_adjoint_restrictIndicatorCLM,
        cc20LogWindowRestrict_restrictIndicator]

theorem cc20GlobalLogWindowQuantizedRemainder_apply_of_support_subset
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2)
    (hsupport : Function.support (u : ℝ → ℂ) ⊆ cc20LogWindow lambda) :
    cc20GlobalLogWindowQuantizedRemainder lambda hlambda u =
      cc20GlobalLogWindowL2Operator lambda hlambda u - (2 : ℂ) • u := by
  rw [cc20GlobalLogWindowQuantizedRemainder_apply,
    cc20LogWindowProjection_eq_self_of_support_subset
      lambda hlambda u hsupport]

theorem cc20GlobalLogWindowQuantizedRemainder_inner_re_of_support_subset
    (lambda : ℝ) (hlambda : 1 < lambda) (u : cc20GlobalLogL2)
    (hsupport : Function.support (u : ℝ → ℂ) ⊆ cc20LogWindow lambda) :
    (⟪u, cc20GlobalLogWindowQuantizedRemainder lambda hlambda u⟫_ℂ).re =
      (⟪u, cc20GlobalLogWindowL2Operator lambda hlambda u⟫_ℂ).re -
        2 * ‖u‖ ^ 2 := by
  rw [cc20GlobalLogWindowQuantizedRemainder_apply_of_support_subset
      lambda hlambda u hsupport,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    Complex.sub_re, Complex.mul_re]
  norm_num
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

end CC20Concrete
end Source
end ConnesWeilRH
