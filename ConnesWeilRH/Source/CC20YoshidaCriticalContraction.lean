/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Critical-line contraction for support-growing Yoshida factors

This module constructs the translated-pair factor used to keep prescribed
off-critical orbit values while making the complete critical-line transform
strictly contractive.  It is deliberately stated before any finite-S trace
estimate: the contraction is a source producer, not a stored remainder sign.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaCriticalContraction

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open scoped ComplexConjugate ContDiff

namespace CompactLogTest

/-- Translate a compact logarithmic test to the right by `a`. -/
noncomputable def translate (f : CompactLogTest) (a : ℝ) : CompactLogTest := by
  let raw : ℝ → ℂ := fun x => f.test (x - a)
  have hcompact : HasCompactSupport raw := by
    simpa [raw, sub_eq_add_neg] using
      f.compactSupport.comp_homeomorph (Homeomorph.addRight (-a))
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    fun_prop
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem translate_apply (f : CompactLogTest) (a x : ℝ) :
    (translate f a).test x = f.test (x - a) :=
  rfl

/-- Translation becomes multiplication by the corresponding exponential
character under the bilateral Laplace transform. -/
theorem laplaceAt_translate (f : CompactLogTest) (a : ℝ) (s : ℂ) :
    laplaceAt (translate f a) s =
      Complex.exp (s * (a : ℂ)) * laplaceAt f s := by
  unfold laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
    translate_apply]
  let shifted : ℝ → ℂ := fun x =>
    Complex.exp (s * ((x + a : ℝ) : ℂ)) * f.test x
  have hchange :
      (fun x : ℝ => Complex.exp (s * (x : ℂ)) * f.test (x - a)) =
        fun x : ℝ => shifted (x - a) := by
    funext x
    simp only [shifted]
    congr 2
    push_cast
    ring
  rw [hchange]
  have hshift : (∫ x : ℝ, shifted (x - a)) = ∫ x : ℝ, shifted x := by
    simpa [sub_eq_add_neg] using integral_add_right_eq_self shifted (-a)
  rw [hshift]
  calc
    (∫ x : ℝ, shifted x) =
        ∫ x : ℝ, Complex.exp (s * (a : ℂ)) *
          (Complex.exp (s * (x : ℂ)) * f.test x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [shifted]
      have hexponent :
          s * ((x + a : ℝ) : ℂ) = s * (a : ℂ) + s * (x : ℂ) := by
        push_cast
        ring
      rw [hexponent, Complex.exp_add]
      ring
    _ = Complex.exp (s * (a : ℂ)) *
        ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x :=
      integral_const_mul _ _

/-- The centered translated pair.  Its transform is a hyperbolic-cosine
factor, normalized to equal one at centered real displacement `delta` when
the imaginary phase is resonant. -/
noncomputable def centeredPair
    (f : CompactLogTest) (shift delta : ℝ) : CompactLogTest := by
  let plus := translate f shift
  let minus := translate f (-shift)
  let denominator : ℂ := (2 * Real.cosh (shift * delta) : ℝ)
  let raw : ℝ → ℂ := fun x =>
    denominator⁻¹ * (plus.test x + minus.test x)
  have hcompact : HasCompactSupport raw := by
    exact (plus.compactSupport.add minus.compactSupport).mul_left
  have hsmooth : ContDiff ℝ ∞ raw := by
    dsimp [raw]
    exact contDiff_const.mul ((plus.test.smooth ⊤).add (minus.test.smooth ⊤))
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa [raw] using hcompact }

@[simp] theorem centeredPair_apply
    (f : CompactLogTest) (shift delta x : ℝ) :
    (centeredPair f shift delta).test x =
      ((2 * Real.cosh (shift * delta) : ℂ)⁻¹) *
        (f.test (x - shift) + f.test (x + shift)) := by
  simp [centeredPair, translate_apply]

/-- Exact transform of the centered translated pair. -/
theorem laplaceAt_centeredPair
    (f : CompactLogTest) (shift delta : ℝ) (s : ℂ) :
    laplaceAt (centeredPair f shift delta) s =
      ((2 * Real.cosh (shift * delta) : ℂ)⁻¹) *
        (Complex.exp (s * (shift : ℂ)) +
          Complex.exp (s * ((-shift : ℝ) : ℂ))) * laplaceAt f s := by
  unfold laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
    centeredPair_apply]
  have htranslated (a : ℝ) : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * f.test (x - a)) := by
    simpa only [← CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
      ← translate_apply] using
      (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
        (translate f a) s).test.integrable (μ := volume)
  have hplus : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * f.test (x - shift)) :=
    htranslated shift
  have hminus : Integrable (fun x : ℝ =>
      Complex.exp (s * (x : ℂ)) * f.test (x + shift)) := by
    simpa only [sub_neg_eq_add] using htranslated (-shift)
  rw [show (fun x : ℝ => Complex.exp (s * (x : ℂ)) *
      ((2 * Real.cosh (shift * delta) : ℂ)⁻¹ *
        (f.test (x - shift) + f.test (x + shift)))) =
      fun x : ℝ => (2 * Real.cosh (shift * delta) : ℂ)⁻¹ *
        (Complex.exp (s * (x : ℂ)) * f.test (x - shift) +
          Complex.exp (s * (x : ℂ)) * f.test (x + shift)) by
    funext x; ring]
  rw [integral_const_mul, integral_add hplus hminus]
  have htranslatePlus := laplaceAt_translate f shift s
  unfold laplaceAt at htranslatePlus
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
    translate_apply] at htranslatePlus
  have htranslateMinus := laplaceAt_translate f (-shift) s
  unfold laplaceAt at htranslateMinus
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
    translate_apply, sub_neg_eq_add] at htranslateMinus
  rw [htranslatePlus, htranslateMinus]
  ring

/-- An integral multiple of the full imaginary period gives exact resonance. -/
theorem exp_mul_I_eq_one_of_mul_eq_nat_two_pi
    (shift gamma : ℝ) (n : ℕ)
    (hresonance : gamma * shift = (n : ℝ) * (2 * Real.pi)) :
    Complex.exp (((gamma * shift : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [hresonance]
  push_cast
  simpa only [mul_assoc] using Complex.exp_nat_mul_two_pi_mul_I n

/-- At a resonant centered point `delta + i gamma`, the two translated
exponentials add to the real hyperbolic-cosine normalizer. -/
theorem centered_exponential_sum_eq_two_cosh_of_phase
    (shift delta gamma : ℝ)
    (hphase :
      Complex.exp (((gamma * shift : ℝ) : ℂ) * Complex.I) = 1) :
    Complex.exp
          (((delta : ℂ) + (gamma : ℂ) * Complex.I) * (shift : ℂ)) +
        Complex.exp
          (((delta : ℂ) + (gamma : ℂ) * Complex.I) *
            ((-shift : ℝ) : ℂ)) =
      (2 * Real.cosh (shift * delta) : ℝ) := by
  have hnegphase :
      Complex.exp (((-gamma * shift : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-gamma * shift : ℝ) : ℂ) * Complex.I) =
        -(((gamma * shift : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, hphase, inv_one]
  have hplusExponent :
      ((delta : ℂ) + (gamma : ℂ) * Complex.I) * (shift : ℂ) =
        ((shift * delta : ℝ) : ℂ) +
          ((gamma * shift : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hminusExponent :
      ((delta : ℂ) + (gamma : ℂ) * Complex.I) * ((-shift : ℝ) : ℂ) =
        ((-(shift * delta) : ℝ) : ℂ) +
          ((-gamma * shift : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hplusExponent, hminusExponent, Complex.exp_add, Complex.exp_add,
    hphase, hnegphase, mul_one, mul_one]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast
  rw [Real.cosh_eq]
  ring

/-- The `L¹` mass used for the global critical-line estimate. -/
noncomputable def l1Mass (f : CompactLogTest) : ℝ :=
  ∫ x : ℝ, ‖f.test x‖

theorem l1Mass_nonneg (f : CompactLogTest) : 0 ≤ l1Mass f := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- Translation preserves the `L¹` mass of a compact logarithmic test. -/
theorem l1Mass_translate_eq (f : CompactLogTest) (a : ℝ) :
    l1Mass (translate f a) = l1Mass f := by
  unfold l1Mass
  simpa only [translate_apply, sub_eq_add_neg] using
    integral_add_right_eq_self (fun x : ℝ => ‖f.test x‖) (-a)

/-- The normalized centered pair is an actual `L¹` contraction.  This is the
input needed for Young's convolution inequality; the critical-line transform
bound alone would not control the selected source root. -/
theorem l1Mass_centeredPair_le
    (f : CompactLogTest) (shift delta : ℝ) :
    l1Mass (centeredPair f shift delta) ≤
      l1Mass f / Real.cosh (shift * delta) := by
  let c : ℝ := Real.cosh (shift * delta)
  have hc : 0 < c := Real.cosh_pos _
  have hplus : Integrable (fun x : ℝ => ‖f.test (x - shift)‖) := by
    simpa only [translate_apply] using (translate f shift).test.integrable.norm
  have hminus : Integrable (fun x : ℝ => ‖f.test (x + shift)‖) := by
    simpa only [translate_apply, sub_neg_eq_add] using
      (translate f (-shift)).test.integrable.norm
  have hright : Integrable (fun x : ℝ =>
      (2 * c)⁻¹ * (‖f.test (x - shift)‖ + ‖f.test (x + shift)‖)) :=
    (hplus.add hminus).const_mul _
  have hleft : Integrable (fun x : ℝ =>
      ‖(centeredPair f shift delta).test x‖) :=
    (centeredPair f shift delta).test.integrable.norm
  have hdenominator : ‖((2 * c : ℂ)⁻¹)‖ = (2 * c)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
  have hpoint (x : ℝ) :
      ‖(centeredPair f shift delta).test x‖ ≤
        (2 * c)⁻¹ * (‖f.test (x - shift)‖ + ‖f.test (x + shift)‖) := by
    rw [centeredPair_apply, norm_mul, hdenominator]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
      (inv_nonneg.mpr (mul_nonneg (by norm_num) hc.le))
  have hplusIntegral :
      (∫ x : ℝ, ‖f.test (x - shift)‖) = l1Mass f := by
    simpa only [l1Mass, translate_apply] using l1Mass_translate_eq f shift
  have hminusIntegral :
      (∫ x : ℝ, ‖f.test (x + shift)‖) = l1Mass f := by
    simpa only [l1Mass, translate_apply, sub_neg_eq_add] using
      l1Mass_translate_eq f (-shift)
  calc
    l1Mass (centeredPair f shift delta) =
        ∫ x : ℝ, ‖(centeredPair f shift delta).test x‖ := rfl
    _ ≤ ∫ x : ℝ,
        (2 * c)⁻¹ * (‖f.test (x - shift)‖ + ‖f.test (x + shift)‖) :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = (2 * c)⁻¹ * (l1Mass f + l1Mass f) := by
      rw [integral_const_mul, integral_add hplus hminus,
        hplusIntegral, hminusIntegral]
    _ = l1Mass f / c := by
      field_simp [ne_of_gt hc]
      ring

/-- A pure-imaginary Laplace value is bounded by the `L¹` mass. -/
theorem norm_laplaceAt_mul_I_le_l1Mass
    (f : CompactLogTest) (t : ℝ) :
    ‖laplaceAt f ((t : ℂ) * Complex.I)‖ ≤ l1Mass f := by
  unfold laplaceAt l1Mass
  calc
    ‖∫ x : ℝ,
        (CC20YoshidaConvolution.CompactLogTest.exponentialWeight
          f ((t : ℂ) * Complex.I)).test x‖ ≤
        ∫ x : ℝ,
          ‖(CC20YoshidaConvolution.CompactLogTest.exponentialWeight
            f ((t : ℂ) * Complex.I)).test x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f.test x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply,
        norm_mul]
      have hexp :
          ‖Complex.exp (((t : ℂ) * Complex.I) * (x : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [hexp, one_mul]

/-- The centered pair is uniformly contractive on the complete imaginary
axis once its translated mass is divided by the real hyperbolic cosine. -/
theorem norm_laplaceAt_centeredPair_mul_I_le
    (f : CompactLogTest) (shift delta t : ℝ) :
    ‖laplaceAt (centeredPair f shift delta)
        ((t : ℂ) * Complex.I)‖ ≤
      l1Mass f / Real.cosh (shift * delta) := by
  rw [laplaceAt_centeredPair]
  let c : ℝ := Real.cosh (shift * delta)
  have hc : 0 < c := Real.cosh_pos _
  have hexp (a : ℝ) :
      ‖Complex.exp (((t : ℂ) * Complex.I) * (a : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hsum :
      ‖Complex.exp (((t : ℂ) * Complex.I) * (shift : ℂ)) +
          Complex.exp (((t : ℂ) * Complex.I) * ((-shift : ℝ) : ℂ))‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (((t : ℂ) * Complex.I) * (shift : ℂ))‖ +
          ‖Complex.exp
            (((t : ℂ) * Complex.I) * ((-shift : ℝ) : ℂ))‖ :=
        norm_add_le _ _
      _ = 2 := by rw [hexp, hexp]; norm_num
  have hdenominator :
      ‖((2 * c : ℂ)⁻¹)‖ = (2 * c)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
  have hseed := norm_laplaceAt_mul_I_le_l1Mass f t
  rw [norm_mul, norm_mul, hdenominator]
  calc
    (2 * c)⁻¹ *
        ‖Complex.exp (((t : ℂ) * Complex.I) * (shift : ℂ)) +
          Complex.exp
            (((t : ℂ) * Complex.I) * ((-shift : ℝ) : ℂ))‖ *
          ‖laplaceAt f ((t : ℂ) * Complex.I)‖ ≤
        (2 * c)⁻¹ * 2 * l1Mass f := by
      gcongr
    _ = l1Mass f / c := by
      field_simp [ne_of_gt hc]

/-- If the seed is one and the translated exponential sum equals its
normalizing hyperbolic cosine, the centered pair remains exactly one. -/
theorem laplaceAt_centeredPair_eq_one
    (f : CompactLogTest) (shift delta : ℝ) (s : ℂ)
    (hseed : laplaceAt f s = 1)
    (hresonance :
      Complex.exp (s * (shift : ℂ)) +
          Complex.exp (s * ((-shift : ℝ) : ℂ)) =
        (2 * Real.cosh (shift * delta) : ℝ)) :
    laplaceAt (centeredPair f shift delta) s = 1 := by
  rw [laplaceAt_centeredPair, hseed, hresonance]
  have hne : (2 * Real.cosh (shift * delta) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (Real.cosh_pos _))
  push_cast at hne ⊢
  rw [inv_mul_cancel₀ hne]
  simp

/-- A seed normalized at `delta + i gamma` remains normalized after the
centered-pair construction whenever the translation is resonant. -/
theorem laplaceAt_centeredPair_eq_one_of_phase
    (f : CompactLogTest) (shift delta gamma : ℝ)
    (hseed :
      laplaceAt f ((delta : ℂ) + (gamma : ℂ) * Complex.I) = 1)
    (hphase :
      Complex.exp (((gamma * shift : ℝ) : ℂ) * Complex.I) = 1) :
    laplaceAt (centeredPair f shift delta)
        ((delta : ℂ) + (gamma : ℂ) * Complex.I) = 1 := by
  exact laplaceAt_centeredPair_eq_one f shift delta
    ((delta : ℂ) + (gamma : ℂ) * Complex.I) hseed
    (centered_exponential_sum_eq_two_cosh_of_phase
      shift delta gamma hphase)

/-- One resonant centered pair preserves all four sign choices in the
functional-equation/conjugation orbit. -/
theorem laplaceAt_centeredPair_eq_one_on_fourPointOrbit
    (f : CompactLogTest) (shift delta gamma : ℝ)
    (hplusPlus :
      laplaceAt f ((delta : ℂ) + (gamma : ℂ) * Complex.I) = 1)
    (hminusPlus :
      laplaceAt f ((-delta : ℝ) + (gamma : ℂ) * Complex.I) = 1)
    (hplusMinus :
      laplaceAt f ((delta : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) = 1)
    (hminusMinus :
      laplaceAt f
        (((-delta : ℝ) : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) = 1)
    (hphase :
      Complex.exp (((gamma * shift : ℝ) : ℂ) * Complex.I) = 1) :
    laplaceAt (centeredPair f shift delta)
          ((delta : ℂ) + (gamma : ℂ) * Complex.I) = 1 ∧
      laplaceAt (centeredPair f shift delta)
          (((-delta : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) = 1 ∧
      laplaceAt (centeredPair f shift delta)
          ((delta : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) = 1 ∧
      laplaceAt (centeredPair f shift delta)
          (((-delta : ℝ) : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) = 1 := by
  have hnegphase :
      Complex.exp (((-gamma * shift : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((-gamma * shift : ℝ) : ℂ) * Complex.I) =
        -(((gamma * shift : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, hphase, inv_one]
  have hsumPlus (signedGamma : ℝ)
      (hsignedPhase :
        Complex.exp (((signedGamma * shift : ℝ) : ℂ) * Complex.I) = 1) :
      Complex.exp
            (((delta : ℂ) + (signedGamma : ℂ) * Complex.I) *
              (shift : ℂ)) +
          Complex.exp
            (((delta : ℂ) + (signedGamma : ℂ) * Complex.I) *
              ((-shift : ℝ) : ℂ)) =
        (2 * Real.cosh (shift * delta) : ℝ) := by
    exact centered_exponential_sum_eq_two_cosh_of_phase
      shift delta signedGamma hsignedPhase
  have hsumMinus (signedGamma : ℝ)
      (hsignedPhase :
        Complex.exp (((signedGamma * shift : ℝ) : ℂ) * Complex.I) = 1) :
      Complex.exp
            ((((-delta : ℝ) : ℂ) + (signedGamma : ℂ) * Complex.I) *
              (shift : ℂ)) +
          Complex.exp
            ((((-delta : ℝ) : ℂ) + (signedGamma : ℂ) * Complex.I) *
              ((-shift : ℝ) : ℂ)) =
        (2 * Real.cosh (shift * delta) : ℝ) := by
    have h := centered_exponential_sum_eq_two_cosh_of_phase
      shift (-delta) signedGamma hsignedPhase
    simpa only [mul_neg, Real.cosh_neg] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact laplaceAt_centeredPair_eq_one f shift delta
      ((delta : ℂ) + (gamma : ℂ) * Complex.I) hplusPlus
      (hsumPlus gamma hphase)
  · exact laplaceAt_centeredPair_eq_one f shift delta
      (((-delta : ℝ) : ℂ) + (gamma : ℂ) * Complex.I) hminusPlus
      (hsumMinus gamma hphase)
  · exact laplaceAt_centeredPair_eq_one f shift delta
      ((delta : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) hplusMinus
      (hsumPlus (-gamma) hnegphase)
  · exact laplaceAt_centeredPair_eq_one f shift delta
      (((-delta : ℝ) : ℂ) + ((-gamma : ℝ) : ℂ) * Complex.I) hminusMinus
      (hsumMinus (-gamma) hnegphase)

/-- Undo the selected half-density shift on a centered compact test. -/
noncomputable def rawOfCentered (f : CompactLogTest) : CompactLogTest :=
  CC20YoshidaConvolution.CompactLogTest.exponentialWeight f (-1 / 2)

@[simp] theorem rawOfCentered_apply (f : CompactLogTest) (x : ℝ) :
    (rawOfCentered f).test x =
      Complex.exp ((-1 / 2 : ℂ) * (x : ℂ)) * f.test x :=
  rfl

theorem laplaceAt_rawOfCentered (f : CompactLogTest) (s : ℂ) :
    laplaceAt (rawOfCentered f) s = laplaceAt f (s - 1 / 2) := by
  unfold rawOfCentered laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The raw coordinate at `1/2 + it` is exactly the centered imaginary-axis
Laplace transform. -/
theorem laplaceAt_rawOfCentered_critical
    (f : CompactLogTest) (t : ℝ) :
    laplaceAt (rawOfCentered f)
        (1 / 2 + (t : ℂ) * Complex.I) =
      laplaceAt f ((t : ℂ) * Complex.I) := by
  rw [laplaceAt_rawOfCentered]
  congr 1
  ring

/-- The raw Yoshida base inherits the support-independent critical-line
contraction of its centered translated pair. -/
theorem norm_laplaceAt_raw_centeredPair_critical_le
    (f : CompactLogTest) (shift delta t : ℝ) :
    ‖laplaceAt (rawOfCentered (centeredPair f shift delta))
        (1 / 2 + (t : ℂ) * Complex.I)‖ ≤
      l1Mass f / Real.cosh (shift * delta) := by
  rw [laplaceAt_rawOfCentered_critical]
  exact norm_laplaceAt_centeredPair_mul_I_le f shift delta t

end CompactLogTest

end CC20YoshidaCriticalContraction
end Source
end ConnesWeilRH
