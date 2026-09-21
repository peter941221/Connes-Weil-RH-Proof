/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseGrowthBound

/-!
# Explicit second derivative and quadratic growth of the scattering phase

The phase quotient is rewritten as a unit-modulus factor times its logarithmic
derivative.  Differentiating this factorization gives the exact second
derivative shape `phase * (Q^2 + Q')`, which is the quantitative interface
needed for the four-term L1 estimate.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open scoped ComplexConjugate

noncomputable def ccm24ArchimedeanPhaseLogDerivative (xi : ℝ) : ℂ :=
  (-Complex.I * (2 * Real.pi : ℂ)) *
      ccm24CriticalGammaRLogDeriv xi -
    conj ((-Complex.I * (2 * Real.pi : ℂ)) *
      ccm24CriticalGammaRLogDeriv xi)

theorem deriv_ccm24ArchimedeanScatteringPhase_factorized (xi : ℝ) :
    deriv ccm24ArchimedeanScatteringPhase xi =
      ccm24ArchimedeanScatteringPhase xi *
        ccm24ArchimedeanPhaseLogDerivative xi := by
  let F : ℝ → ℂ := ccm24ArchimedeanFactor
  let L : ℝ → ℂ := ccm24CriticalGammaRLogDeriv
  let a : ℂ := -Complex.I * (2 * Real.pi : ℂ)
  have hF0 : F xi ≠ 0 := by
    simpa [F] using ccm24ArchimedeanFactor_ne_zero xi
  have hphase := deriv_ccm24ArchimedeanScatteringPhase_formula xi
  have hF' := (hasDerivAt_ccm24ArchimedeanFactor_logDeriv xi).deriv
  have hrewrite :
      (deriv F xi * conj (F xi) - F xi * conj (deriv F xi)) /
          (conj (F xi)) ^ 2 =
        (F xi / conj (F xi)) * (a * L xi - conj (a * L xi)) := by
    rw [hF']
    simp [F, L, a, map_mul, map_neg, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hF0]
  rw [show deriv ccm24ArchimedeanScatteringPhase xi =
      (deriv F xi * conj (F xi) - F xi * conj (deriv F xi)) /
        (conj (F xi)) ^ 2 by simpa [F] using hphase]
  rw [hrewrite]
  change (F xi / conj (F xi)) * (a * L xi - conj (a * L xi)) =
    (F xi / conj (F xi)) * (a * L xi - conj (a * L xi))
  rfl

theorem deriv_deriv_ccm24ArchimedeanScatteringPhase_factorized (xi : ℝ) :
    deriv (deriv ccm24ArchimedeanScatteringPhase) xi =
      ccm24ArchimedeanScatteringPhase xi *
        (ccm24ArchimedeanPhaseLogDerivative xi ^ 2 +
          ((-Complex.I * (2 * Real.pi : ℂ)) *
              deriv ccm24CriticalGammaRLogDeriv xi -
            conj ((-Complex.I * (2 * Real.pi : ℂ)) *
              deriv ccm24CriticalGammaRLogDeriv xi))) := by
  let P : ℝ → ℂ := ccm24ArchimedeanScatteringPhase
  let L : ℝ → ℂ := ccm24CriticalGammaRLogDeriv
  let a : ℂ := -Complex.I * (2 * Real.pi : ℂ)
  let Q : ℝ → ℂ := fun x => a * L x - conj (a * L x)
  have hL : HasDerivAt L (deriv L xi) xi := by
    have hL0 := hasDerivAt_ccm24CriticalGammaRLogDeriv xi
    have heq : deriv L xi =
        (-Complex.I * (Real.pi : ℂ)) * (1 / 2 : ℂ) *
          deriv Complex.digamma
            ((1 / 4 : ℂ) - Complex.I * (Real.pi * xi : ℝ)) := by
      simpa [L] using hL0.deriv
    rw [heq]
    simpa [L] using hL0
  have hAL : HasDerivAt (fun x : ℝ => a * L x)
      (a * deriv L xi) xi := by
    simpa [a] using hL.const_mul a
  have hconjAL : HasDerivAt (fun x : ℝ => conj (a * L x))
      (conj (a * deriv L xi)) xi := by
    let g : ℝ → ℂ := fun x => a * L x
    have hg : HasDerivAt g (a * deriv L xi) xi := by
      simpa [g] using hAL
    have hcomp :
        fderiv ℝ (⇑Complex.conjCLE ∘ g) xi =
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘SL fderiv ℝ g xi :=
      Complex.conjCLE.comp_fderiv
    have heq :
        fderiv ℝ (⇑Complex.conjCLE ∘ g) xi =
          ContinuousLinearMap.toSpanSingleton ℝ (conj (a * deriv L xi)) := by
      rw [hcomp]
      apply ContinuousLinearMap.ext
      intro y
      change Complex.conjCLE (fderiv ℝ g xi y) = _
      rw [fderiv_eq_smul_deriv]
      have hgderiv : deriv g xi = a * deriv L xi := by
        simpa [g] using hg.deriv
      simp [Complex.conjCLE_apply, smul_eq_mul, hgderiv]
    have hfd :=
      (Complex.conjCLE.differentiableAt.comp xi hg.differentiableAt).hasFDerivAt
    have hfd' : HasFDerivAt (⇑Complex.conjCLE ∘ g)
        (ContinuousLinearMap.toSpanSingleton ℝ (conj (a * deriv L xi))) xi := by
      rw [← heq]
      exact hfd
    apply (hasDerivAt_iff_hasFDerivAt).2
    simpa [Function.comp_def, Complex.conjCLE_apply, g] using hfd'
  have hQ : HasDerivAt Q
      (a * deriv L xi - conj (a * deriv L xi)) xi := by
    simpa [Q] using hAL.sub hconjAL
  have hP : HasDerivAt P (P xi * Q xi) xi := by
    have h := (differentiable_ccm24ArchimedeanScatteringPhase xi).hasDerivAt
    rw [deriv_ccm24ArchimedeanScatteringPhase_factorized xi] at h
    simpa [P, Q, a, L, ccm24ArchimedeanPhaseLogDerivative] using h
  have hprod := hP.mul hQ
  have hfun : deriv P = fun x : ℝ => P x * Q x := by
    funext x
    simpa [P, Q, a, L, ccm24ArchimedeanPhaseLogDerivative] using
      deriv_ccm24ArchimedeanScatteringPhase_factorized x
  rw [hfun]
  have hvalue := hprod.deriv
  convert hvalue using 1 <;>
    simp [P, L, Q, a, ccm24ArchimedeanPhaseLogDerivative,
      Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] <;>
    ring

theorem norm_deriv_deriv_ccm24ArchimedeanScatteringPhase_le_quadratic
    (xi : ℝ) :
    ‖deriv (deriv ccm24ArchimedeanScatteringPhase) xi‖ ≤
      (4 * Real.pi *
          (‖ccm24CriticalGammaRLogDeriv 0‖ +
            (18 * Real.pi) * |xi|)) ^ 2 +
        4 * Real.pi * (18 * Real.pi) := by
  let a : ℂ := -Complex.I * (2 * Real.pi : ℂ)
  let L : ℝ → ℂ := ccm24CriticalGammaRLogDeriv
  have ha : ‖a‖ = 2 * Real.pi := by
    simp [a, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hQ :
      ‖ccm24ArchimedeanPhaseLogDerivative xi‖ ≤
        4 * Real.pi * ‖L xi‖ := by
    calc
      ‖ccm24ArchimedeanPhaseLogDerivative xi‖ =
          ‖a * L xi - conj (a * L xi)‖ := by
            rfl
      _ ≤ ‖a * L xi‖ + ‖conj (a * L xi)‖ := norm_sub_le _ _
      _ = 2 * ‖a‖ * ‖L xi‖ := by
        rw [Complex.norm_conj, norm_mul]
        ring
      _ = 4 * Real.pi * ‖L xi‖ := by rw [ha]; ring
  have hQ' :
      ‖((-Complex.I * (2 * Real.pi : ℂ)) *
          deriv ccm24CriticalGammaRLogDeriv xi -
        conj ((-Complex.I * (2 * Real.pi : ℂ)) *
          deriv ccm24CriticalGammaRLogDeriv xi))‖ ≤
        4 * Real.pi * ‖deriv ccm24CriticalGammaRLogDeriv xi‖ := by
    calc
      ‖((-Complex.I * (2 * Real.pi : ℂ)) *
          deriv ccm24CriticalGammaRLogDeriv xi -
        conj ((-Complex.I * (2 * Real.pi : ℂ)) *
          deriv ccm24CriticalGammaRLogDeriv xi))‖ ≤
          ‖a * deriv L xi‖ + ‖conj (a * deriv L xi)‖ := by
            apply norm_sub_le
      _ = 2 * ‖a‖ * ‖deriv L xi‖ := by
        rw [Complex.norm_conj, norm_mul]
        ring
      _ = 4 * Real.pi * ‖deriv ccm24CriticalGammaRLogDeriv xi‖ := by
        rw [ha]
        change 2 * (2 * Real.pi) *
            ‖deriv ccm24CriticalGammaRLogDeriv xi‖ =
          4 * Real.pi * ‖deriv ccm24CriticalGammaRLogDeriv xi‖
        ring
  have hphaseNorm : ‖ccm24ArchimedeanScatteringPhase xi‖ = 1 :=
    norm_ccm24ArchimedeanScatteringPhase xi
  have hL := norm_ccm24CriticalGammaRLogDeriv_le_linear xi
  have hLd := norm_deriv_ccm24CriticalGammaRLogDeriv_le xi
  rw [deriv_deriv_ccm24ArchimedeanScatteringPhase_factorized xi,
    norm_mul, hphaseNorm, one_mul]
  calc
    ‖ccm24ArchimedeanPhaseLogDerivative xi ^ 2 +
        ((-Complex.I * (2 * Real.pi : ℂ)) *
            deriv ccm24CriticalGammaRLogDeriv xi -
          conj ((-Complex.I * (2 * Real.pi : ℂ)) *
            deriv ccm24CriticalGammaRLogDeriv xi))‖ ≤
        ‖ccm24ArchimedeanPhaseLogDerivative xi ^ 2‖ +
          ‖((-Complex.I * (2 * Real.pi : ℂ)) *
              deriv ccm24CriticalGammaRLogDeriv xi -
            conj ((-Complex.I * (2 * Real.pi : ℂ)) *
              deriv ccm24CriticalGammaRLogDeriv xi))‖ := norm_add_le _ _
    _ ≤ (4 * Real.pi * ‖L xi‖) ^ 2 +
          4 * Real.pi * ‖deriv ccm24CriticalGammaRLogDeriv xi‖ := by
      rw [norm_pow]
      have hsq :
          ‖ccm24ArchimedeanPhaseLogDerivative xi‖ ^ 2 ≤
            (4 * Real.pi * ‖L xi‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hQ
      exact add_le_add hsq hQ'
    _ ≤ (4 * Real.pi *
          (‖ccm24CriticalGammaRLogDeriv 0‖ +
            (18 * Real.pi) * |xi|)) ^ 2 +
          4 * Real.pi * (18 * Real.pi) := by
      apply add_le_add
      · gcongr
      · gcongr

end Dev
end ConnesWeilRH
