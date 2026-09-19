/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# First-order regularity of the archimedean scattering phase

The Hardy multiplier currently has an L2 definition and a continuity theorem.
This leaf supplies the next literal interface: the Gamma factor and its unit
modulus quotient are differentiable on the real frequency axis.  No growth
bound is asserted here; that remains a separate analytic obligation.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open scoped ComplexConjugate

private theorem criticalGamma_argument_avoids_poles (xi : ℝ) :
    ∀ m : ℕ,
      (((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ)) / 2) ≠ -(m : ℂ) := by
  intro m h
  have hre := congrArg Complex.re h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  norm_num [Complex.mul_re] at hre
  linarith

theorem differentiable_ccm24ArchimedeanFactor :
    Differentiable ℝ ccm24ArchimedeanFactor := by
  intro xi
  change DifferentiableAt ℝ
    (fun x : ℝ =>
      (Real.pi : ℂ) ^
          (-((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * x : ℝ)) / 2) *
        Complex.Gamma
          (((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * x : ℝ)) / 2)) xi
  apply DifferentiableAt.mul
  ·
    let z : ℂ → ℂ := fun z =>
      ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi : ℂ) * z) / 2
    have hz : DifferentiableAt ℂ z (xi : ℂ) := by
      dsimp [z]
      fun_prop
    have hzR : DifferentiableAt ℝ (fun x : ℝ => z (x : ℂ)) xi := by
      let a : ℂ := -Complex.I * (2 * Real.pi : ℂ) / 2
      have hlin : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a xi := by
        simpa using ((hasDerivAt_id (xi : ℂ)).const_mul a).comp_ofReal
      have hsum := (hasDerivAt_const (x := xi) (c := (1 / 4 : ℂ))).add hlin
      convert hsum.differentiableAt using 1
      · funext x
        simp [z, a]
        ring
    have hq : DifferentiableAt ℂ
        (fun z : ℂ => (Real.pi : ℂ) ^ (-z))
        (z (xi : ℂ)) := by
      have hexp : DifferentiableAt ℂ (fun z : ℂ => -z) (z (xi : ℂ)) := by
        fun_prop
      exact hexp.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hqr : DifferentiableAt ℝ
        (fun x : ℝ => (Real.pi : ℂ) ^ (-(z (x : ℂ)))) xi := by
      exact (hq.hasDerivAt.complexToReal_fderiv.comp_hasDerivAt xi hzR.hasDerivAt).differentiableAt
    convert hqr using 1
    · congr 1
      funext x
      simp [z]
      ring
  · have hgamma : DifferentiableAt ℂ Complex.Gamma
        (((1 / 2 : ℂ) - Complex.I * (2 * Real.pi * xi : ℝ)) / 2) :=
      Complex.differentiableAt_Gamma _
        (criticalGamma_argument_avoids_poles xi)
    let z : ℂ → ℂ := fun z =>
      ((1 / 2 : ℂ) - Complex.I * (2 * Real.pi : ℂ) * z) / 2
    have hz : DifferentiableAt ℂ z (xi : ℂ) := by
      dsimp [z]
      fun_prop
    have hzR : DifferentiableAt ℝ (fun x : ℝ => z (x : ℂ)) xi := by
      let a : ℂ := -Complex.I * (2 * Real.pi : ℂ) / 2
      have hlin : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a xi := by
        simpa using ((hasDerivAt_id (xi : ℂ)).const_mul a).comp_ofReal
      have hsum := (hasDerivAt_const (x := xi) (c := (1 / 4 : ℂ))).add hlin
      convert hsum.differentiableAt using 1
      · funext x
        simp [z, a]
        ring
    have hgammaZ : DifferentiableAt ℂ Complex.Gamma (z (xi : ℂ)) := by
      convert hgamma using 1
      simp [z]
      ring
    have hgr : DifferentiableAt ℝ
        (fun x : ℝ => Complex.Gamma (z (x : ℂ))) xi := by
      exact (hgammaZ.hasDerivAt.complexToReal_fderiv.comp_hasDerivAt xi hzR.hasDerivAt).differentiableAt
    convert hgr using 1
    congr 1
    funext x
    simp [z]
    ring_nf

theorem differentiable_ccm24ArchimedeanScatteringPhase :
    Differentiable ℝ ccm24ArchimedeanScatteringPhase := by
  intro xi
  apply DifferentiableAt.div
  · exact differentiable_ccm24ArchimedeanFactor xi
  · exact Complex.conjCLE.differentiableAt.comp xi
      (differentiable_ccm24ArchimedeanFactor xi)
  · simpa using (ccm24ArchimedeanFactor_ne_zero xi)

theorem differentiable_ccm24ArchimedeanScatteringPhase_inverse :
    Differentiable ℝ
      (fun xi => conj (ccm24ArchimedeanScatteringPhase xi)) := by
  intro xi
  change DifferentiableAt ℝ
    (fun x => conj (ccm24ArchimedeanScatteringPhase x)) xi
  exact Complex.conjCLE.differentiableAt.comp xi
    (differentiable_ccm24ArchimedeanScatteringPhase xi)

theorem deriv_ccm24ArchimedeanScatteringPhase_formula (xi : ℝ) :
    deriv ccm24ArchimedeanScatteringPhase xi =
      (deriv ccm24ArchimedeanFactor xi *
          conj (ccm24ArchimedeanFactor xi) -
        ccm24ArchimedeanFactor xi *
          conj (deriv ccm24ArchimedeanFactor xi)) /
        (conj (ccm24ArchimedeanFactor xi)) ^ 2 := by
  let f : ℝ → ℂ := ccm24ArchimedeanFactor
  have hf : HasDerivAt f (deriv f xi) xi :=
    (differentiable_ccm24ArchimedeanFactor xi).hasDerivAt
  have hcf : HasDerivAt (fun x : ℝ => conj (f x))
      (conj (deriv f xi)) xi := by
    have hcomp :
        fderiv ℝ (⇑Complex.conjCLE ∘ f) xi =
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL fderiv ℝ f xi :=
      Complex.conjCLE.comp_fderiv
    have heq :
        fderiv ℝ (⇑Complex.conjCLE ∘ f) xi =
          ContinuousLinearMap.toSpanSingleton ℝ (conj (deriv f xi)) := by
      rw [hcomp]
      apply ContinuousLinearMap.ext
      intro y
      change Complex.conjCLE (fderiv ℝ f xi y) = _
      rw [fderiv_eq_smul_deriv]
      simp [Complex.conjCLE_apply, smul_eq_mul]
    have hfd :=
      (Complex.conjCLE.differentiableAt.comp xi hf.differentiableAt).hasFDerivAt
    have hfd' : HasFDerivAt (⇑Complex.conjCLE ∘ f)
        (ContinuousLinearMap.toSpanSingleton ℝ (conj (deriv f xi))) xi := by
      rw [← heq]
      exact hfd
    apply (hasDerivAt_iff_hasFDerivAt).2
    simpa [Function.comp_def, Complex.conjCLE_apply] using hfd'
  have hquot := hf.div hcf (by
    simpa [f] using ccm24ArchimedeanFactor_ne_zero xi)
  simpa [f, ccm24ArchimedeanScatteringPhase] using hquot.deriv

end Dev
end ConnesWeilRH
