/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1CC20LpOperator
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
-- The "almost everywhere" quantifier `∀ᵐ a ∂μ, p` is declared here.
import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# CC20 kf_I L² operator-norm bound (integrated form)

Integrating the pointwise Hilbert--Schmidt estimate over the output coordinate `x`
gives the operator-norm statement: an `L²(ℝ×ℝ)` kernel applied to an `L²` input is a
bounded map, with

    ‖Af‖₂  ≤  ‖k‖_{L²(ℝ×ℝ)} · ‖f‖₂.

In squared form this leaf proves the extended-real (lintegral) version

    ∫⁻ₓ ‖(Af)(x)‖ₑ²  ≤  (∫⁻₍ₓ,ᵧ₎ ‖k(x,y)‖ₑ²) · (∫⁻_y ‖f(y)‖ₑ²),

which is exactly `‖Af‖₂² ≤ ‖k‖_{HS}² · ‖f‖₂²` written in the nonnegative/extended-reals
setting.  Working in `ℝ≥0∞` (lintegrals) rather than real Bochner integrals is deliberate:
a Bochner integral of a non-integrable function silently defaults to `0`, which would make
the estimate vacuous precisely in the regime we are proving; lintegrals carry the correct
`+∞` behaviour for nonnegative functions and their monotonicity (`lintegral_mono_ae`) needs
no measurability hypothesis.

The extra machinery over the pointwise brick (`C1CC20LpOperator`) has three parts:

* a **section** lemma (`rows_l2_ae_of_kernel_l2`): an `L²(ℝ×ℝ)` kernel has, for almost every
  output coordinate `x`, an `x`-row that lies in `L²`.  This is the sectionwise consequence of
  Fubini used to apply the pointwise Cauchy--Schwarz bound under a measure-almost-everywhere
  quantifier;

* a **Bochner→lintegral bridge** (`bochner_sq_norm_eq_lintegral_enorm_sq`): for an integrable
  square-norm, the real Bochner integral of `‖g‖²` equals the lintegral of the squared extended
  norm.  The pointwise identity `ENNReal.ofReal (‖g y‖²) = ‖g y‖ₑ²` is a simp-lemma; pushing
  the `ofReal` coercion out from under the Bochner integral uses
  `ofReal_integral_eq_lintegral_ofReal`;

* a **Fubini** step (`lintegral_prod`) turning the iterated lintegral of the squared kernel
  into its double (product-measure) lintegral.

This file contains no RH-level sign or coverage claim; it completes the boundedness
foundation for CC20's `kf_I`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20LpOperatorNorm

open MeasureTheory

-- `applyKernel` / `applyKernel_pointwise_l2_bound` live in the sibling leaf; open it so the
-- pointwise Cauchy--Schwarz bound is available unqualified here.
open C1CC20LpOperator

/-- For nonnegative reals, squaring a product of square roots recovers the product:
`(√a · √b)² = a·b`.  Used to turn the squared pointwise Cauchy--Schwarz bound into its mass form -/
lemma half_pow_sq_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a ^ (1 / 2 : ℝ)) * (b ^ (1 / 2 : ℝ))) ^ 2 = a * b := by
  simp only [← Real.sqrt_eq_rpow]   -- ⊢ (√a · √b)² = a·b
  rw [show (Real.sqrt a * Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2 by ring]
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- A Bochner integral of a squared real norm equals the lintegral of the squared extended norm,
for an integrable square-norm.  The pointwise identity `ENNReal.ofReal (‖g y‖²) = ‖g y‖ₑ²` is
simp-automatic; pushing the `ofReal` coercion out from under the Bochner integral uses
`ofReal_integral_eq_lintegral_ofReal`. -/
lemma bochner_sq_norm_eq_lintegral_enorm_sq {g : ℝ → ℂ} (hg : Integrable (fun y => ‖g y‖ ^ 2)) :
    ENNReal.ofReal (∫ y, ‖g y‖ ^ 2) = ∫⁻ y, ‖g y‖ₑ ^ (2 : ℝ) := by
  have hnn : 0 ≤ᵐ[volume] fun y => ‖g y‖ ^ 2 := by
    filter_upwards [] with x
    positivity
  rw [ofReal_integral_eq_lintegral_ofReal hg hnn]   -- ⊢ ∫⁻ (fun y ↦ ofReal(‖g y‖²)) = ∫⁻ ‖g y‖ₑ²
  have hpw : (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) = fun y => ‖g y‖ₑ ^ (2 : ℝ) := by
    ext y; simp   -- the pointwise Bochner→lintegral bridge identity
  rw [hpw]

/-- An `L²(ℝ×ℝ)` kernel has, for almost every output coordinate `x`, an `x`-row that
lies in `L²`.  This is the sectionwise consequence of Fubini used to apply the pointwise
Cauchy--Schwarz bound under a measure-almost-everywhere quantifier. -/
theorem rows_l2_ae_of_kernel_l2 {k : ℝ × ℝ → ℂ} (hk : MemLp k (ENNReal.ofReal 2)) :
    ∀ᵐ x ∂volume, MemLp (fun y => k (x, y)) (ENNReal.ofReal 2) := by
  -- Local nonzero / top facts about `p = ENNReal.ofReal 2` for the `eLpNorm < ∞` iff.
  have hpz : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- (1) a.e. section is strongly measurable: Fubini's section lemma applied to `k`.
  have hsec : ∀ᵐ x ∂volume, AEStronglyMeasurable (fun y => k (x, y)) volume :=
    hk.1.prodMk_left
  -- (2) a.e. section has finite L² mass: Tonelli makes the row-mass function have a finite
  --     integral, hence its value is < ∞ almost everywhere.
  let m : ℝ → ENNReal := fun x => ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)
  -- The squared extended-norm function `p ↦ ‖k p‖ₑ²` is a.e. measurable: the extended norm of an
  -- a.e.-strongly-measurable function is a.e. measurable (`enorm`), and pointwise squaring (a
  -- measurable operation on ℝ≥0∞) preserves it.  The rpow-2 form is rewritten to its self-product
  -- so the product-rule hypothesis applies.
  have hsq : AEMeasurable (fun p => ‖k p‖ₑ ^ (2 : ℝ)) := by
    have heq : (fun p => ‖k p‖ₑ ^ (2 : ℝ)) = fun p => ‖k p‖ₑ * ‖k p‖ₑ := by
      ext p; rw [ENNReal.rpow_two, pow_two]
    rw [heq]
    exact (hk.1.enorm).mul (hk.1.enorm)
  -- Hence the row-mass function m is a.e. measurable (section lemma for lintegrals).
  have hmae_sec : AEMeasurable m volume := by simpa [m] using hsq.lintegral_prod_right'
  -- The double lintegral of the squared norm is finite, since it equals eLpNorm k 2 vol raised to
  -- a power and `hk.2` says that is < ∞.
  have hlt : (∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt).mp hk.2
  -- Tonelli: the total row mass is exactly the double lintegral, hence finite; and thus ≠ ∞.
  have hmtot : ∫⁻ x, m x < ⊤ := by
    rw [show (∫⁻ x, m x) = (∫⁻ z, ‖k z‖ₑ ^ (2 : ℝ)) by
      simpa [m] using (lintegral_prod _ hsq).symm]
    exact hlt
  have hmne : (∫⁻ x, m x) ≠ ⊤ := lt_top_iff_ne_top.mp hmtot
  -- a.e. the row-mass is finite: `ae_lt_top'` takes an AEMeasurable hypothesis and a ≠∞ mass.
  have hrow_fin : ∀ᵐ x ∂volume, m x < ⊤ := ae_lt_top' hmae_sec hmne
  -- Combine: for a.e. x the row is strongly measurable AND has finite squared mass.
  filter_upwards [hsec, hrow_fin] with x hs hm
  refine ⟨hs, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [m] using hm

/-- Integrated (operator-norm) Hilbert--Schmidt bound, squared form in the extended reals.  For an
`L²(ℝ×ℝ)` kernel `k` and an `L²` input `f`, the lintegral of the applied function's squared norm is
at most the product of the kernel's total mass and the input's mass:

    ∫⁻ₓ ‖(Af)(x)‖ₑ²  ≤  (∫⁻₍ₓ,ᵧ₎ ‖k(x,y)‖ₑ²) · (∫⁻_y ‖f(y)‖ₑ²). -/
theorem applyKernel_l2_sq_bound {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal 2)) (hk : MemLp k (ENNReal.ofReal 2)) :
    ∫⁻ x, ‖applyKernel k f x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ p : ℝ × ℝ, ‖k p‖ₑ ^ (2 : ℝ)) * (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)) := by
  have hrows := rows_l2_ae_of_kernel_l2 hk
  -- The squared extended-norm function `p ↦ ‖k p‖ₑ²` is a.e. measurable (see the section lemma); we
  -- reuse it both to factor the constant out of the row-mass lintegral and for Fubini below.
  have hsq : AEMeasurable (fun p => ‖k p‖ₑ ^ (2 : ℝ)) := by
    have heq : (fun p => ‖k p‖ₑ ^ (2 : ℝ)) = fun p => ‖k p‖ₑ * ‖k p‖ₑ := by
      ext p; rw [ENNReal.rpow_two, pow_two]
    rw [heq]
    exact (hk.1.enorm).mul (hk.1.enorm)
  let cinE : ENNReal := ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)
  -- a.e. pointwise bound in the extended reals: square the real Cauchy--Schwarz estimate and coerce
  -- both sides up with `ENNReal.ofReal`, which is monotone on nonnegative reals.
  have hae : ∀ᵐ x ∂volume, ‖applyKernel k f x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := by
    filter_upwards [hrows] with x hxrow
    have hptw := applyKernel_pointwise_l2_bound x hxrow hf
    -- Both Bochner integrals in the pointwise bound are nonnegative because their integrands are
    -- squares.
    have hA : 0 ≤ ∫ y, ‖k (x, y)‖ ^ (2 : ℝ) := by
      exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg (k (x, y))) _
    have hB : 0 ≤ ∫ y, ‖f y‖ ^ (2 : ℝ) := by
      exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg (f y)) _
    have hkrowLp : MemLp (fun y => k (x, y)) 2 volume := by
      simpa using hxrow
    have hkrowInt : Integrable (fun y => ‖k (x, y)‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hxrow.1).mp hkrowLp
    have hfLp : MemLp f 2 volume := by
      simpa using hf
    have hfInt : Integrable (fun y => ‖f y‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hf.1).mp hfLp
    have hAK : ENNReal.ofReal (∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) =
        ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ) := by
      simpa only [Real.rpow_two] using bochner_sq_norm_eq_lintegral_enorm_sq hkrowInt
    have hBF : ENNReal.ofReal (∫ y, ‖f y‖ ^ (2 : ℝ)) = cinE := by
      simpa only [Real.rpow_two, cinE] using bochner_sq_norm_eq_lintegral_enorm_sq hfInt
    calc
      ‖applyKernel k f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖applyKernel k f x‖ ^ 2) := by simp
      _ ≤ ENNReal.ofReal ((∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) * (∫ y, ‖f y‖ ^ (2 : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          ‖applyKernel k f x‖ ^ 2 ≤
              ((∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
                (∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
            gcongr
          _ = (∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) * (∫ y, ‖f y‖ ^ (2 : ℝ)) :=
            half_pow_sq_mul hA hB
      -- Push `ofReal` onto each factor, then bridge the Bochner integrals to lintegrals.
      _ = (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := by
        rw [ENNReal.ofReal_mul hA, hAK, hBF]
  -- The row-mass function is a.e. measurable, so its lintegral against the constant `cinE`
  -- factors out.
  have hrowmass_aemeas : AEMeasurable (fun x => ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) :=
    hsq.lintegral_prod_right'
  -- Integrate the a.e. bound over x and pull out the constant input mass `cinE`.
  have hstep : ∫⁻ x, ‖applyKernel k f x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := by
    calc
      _ ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := lintegral_mono_ae hae
      _ = (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := by
        exact lintegral_mul_const'' cinE hrowmass_aemeas
  -- Fubini: the iterated squared-kernel mass equals its double (product-measure) lintegral.
  have hfub : (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) = (∫⁻ p : ℝ × ℝ, ‖k p‖ₑ ^ (2 : ℝ)) :=
    (lintegral_prod _ hsq).symm
  calc
    ∫⁻ x, ‖applyKernel k f x‖ₑ ^ (2 : ℝ) ≤
        (∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ (2 : ℝ)) * cinE := hstep
    _ = (∫⁻ p : ℝ × ℝ, ‖k p‖ₑ ^ (2 : ℝ)) * cinE := by rw [hfub]

end C1CC20LpOperatorNorm
end Source
end ConnesWeilRH
