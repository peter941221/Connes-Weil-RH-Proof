/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerGenerator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted translation Bessel calculus for the finite-S generator

This module isolates the condition-number-free square estimate available for
the genuine prime-power translation modes.  The abstract Bessel theorem uses
local orthogonal projections, so an eventual Gate 3U consumer must prove that
all physical boundary branches use these same localized vectors.  No such
route-specific factorization is assumed here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSWeightedTranslationBessel

open scoped BigOperators InnerProduct InnerProductSpace
open intervalIntegral
open MeasureTheory
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator

/-- Pointwise local square mass controls the sum of all localized input
energies.  Taking `region i` to be a translated compact support gives the
usual weighted-translation overlap estimate. -/
theorem weightedIndicatorEnergy_le
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (indices : Finset ι) (weight : ι → ℝ)
    (region : ι → Set α) (energy : α → ℝ) (localMass : ℝ)
    (hregion : ∀ i ∈ indices, MeasurableSet (region i))
    (henergy : Integrable energy μ)
    (henergy_nonneg : ∀ᵐ x ∂μ, 0 ≤ energy x)
    (hoverlap : ∀ᵐ x ∂μ,
      (∑ i ∈ indices,
        (region i).indicator (fun _ => weight i) x) ≤ localMass) :
    (∑ i ∈ indices,
      weight i * ∫ x, (region i).indicator energy x ∂μ) ≤
        localMass * ∫ x, energy x ∂μ := by
  have hintegrable (i : ι) (hi : i ∈ indices) :
      Integrable
        (fun x => weight i * (region i).indicator energy x) μ :=
    (henergy.indicator (hregion i hi)).const_mul _
  calc
    (∑ i ∈ indices,
        weight i * ∫ x, (region i).indicator energy x ∂μ) =
        ∑ i ∈ indices,
          ∫ x, weight i * (region i).indicator energy x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ x,
        ∑ i ∈ indices,
          weight i * (region i).indicator energy x ∂μ := by
      rw [integral_finsetSum indices hintegrable]
    _ ≤ ∫ x, localMass * energy x ∂μ := by
      apply MeasureTheory.integral_mono_ae
      · exact integrable_finsetSum indices hintegrable
      · exact henergy.const_mul _
      · filter_upwards [henergy_nonneg, hoverlap] with x hx hmass
        have heq :
            (∑ i ∈ indices,
                weight i * (region i).indicator energy x) =
              energy x *
                (∑ i ∈ indices,
                  (region i).indicator (fun _ => weight i) x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hxi : x ∈ region i
          · simp only [Set.indicator_of_mem hxi]
            ring
          · simp only [Set.indicator_of_notMem hxi, mul_zero]
        rw [heq]
        calc
          energy x *
                (∑ i ∈ indices,
                  (region i).indicator (fun _ => weight i) x) ≤
              energy x * localMass :=
            mul_le_mul_of_nonneg_left hmass hx
          _ = localMass * energy x := by ring
    _ = localMass * ∫ x, energy x ∂μ := by
      rw [MeasureTheory.integral_const_mul]

/-- A finite weighted Bessel estimate from local projection energy.  The
`localEnergy` premise is the Hilbert-space form of the pointwise overlap bound
for compactly supported translates. -/
theorem weightedLocalizedBessel
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (indices : Finset ι) (weight : ι → ℝ)
    (localProjection : ι → H →L[ℂ] H) (vector : ι → H)
    (input : H) (vectorEnergy localMass : ℝ)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (hprojection : ∀ i ∈ indices,
      (localProjection i)† = localProjection i)
    (hlocalized : ∀ i ∈ indices,
      localProjection i (vector i) = vector i)
    (hvectorEnergy : ∀ i ∈ indices,
      ‖vector i‖ ^ 2 ≤ vectorEnergy)
    (hvectorEnergy_nonneg : 0 ≤ vectorEnergy)
    (hlocalEnergy :
      (∑ i ∈ indices, weight i * ‖localProjection i input‖ ^ 2) ≤
        localMass * ‖input‖ ^ 2) :
    (∑ i ∈ indices, weight i * ‖⟪input, vector i⟫_ℂ‖ ^ 2) ≤
      vectorEnergy * localMass * ‖input‖ ^ 2 := by
  calc
    (∑ i ∈ indices, weight i * ‖⟪input, vector i⟫_ℂ‖ ^ 2) ≤
        ∑ i ∈ indices,
          weight i * (vectorEnergy * ‖localProjection i input‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hweight i hi)
      have hinner :
          ⟪input, vector i⟫_ℂ =
            ⟪localProjection i input, vector i⟫_ℂ := by
        have hadjoint :=
          ContinuousLinearMap.adjoint_inner_right
            (localProjection i) input (vector i)
        rw [hprojection i hi, hlocalized i hi] at hadjoint
        exact hadjoint
      have hinnerNorm :
          ‖⟪input, vector i⟫_ℂ‖ ≤
            ‖localProjection i input‖ * ‖vector i‖ := by
        rw [hinner]
        exact norm_inner_le_norm _ _
      calc
        ‖⟪input, vector i⟫_ℂ‖ ^ 2 ≤
            (‖localProjection i input‖ * ‖vector i‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinnerNorm
        _ = ‖localProjection i input‖ ^ 2 * ‖vector i‖ ^ 2 := by ring
        _ ≤ ‖localProjection i input‖ ^ 2 * vectorEnergy :=
          mul_le_mul_of_nonneg_left (hvectorEnergy i hi) (sq_nonneg _)
        _ = vectorEnergy * ‖localProjection i input‖ ^ 2 := by ring
    _ = vectorEnergy *
        (∑ i ∈ indices, weight i * ‖localProjection i input‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ vectorEnergy * (localMass * ‖input‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hlocalEnergy hvectorEnergy_nonneg
    _ = vectorEnergy * localMass * ‖input‖ ^ 2 := by ring

/-!
The preceding analysis estimate is equivalent to a synthesis estimate for
the *same weighted family*.  It does not allow the square weights to be
removed from a coherent sum.  Identical modes give the exact cardinality
loss below; Proof 348 supplies the route-compatible prime-translation
version of the same obstruction.
-/

theorem identicalModes_analysisSquareLedger (n : ℕ) :
    (∑ _ : Fin n, ‖(1 : ℂ)‖ ^ 2) = (n : ℝ) := by
  simp

theorem identicalModes_coherentSynthesisNormSq (n : ℕ) :
    ‖∑ _ : Fin n, (1 : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
  simp

/-- The coherent synthesis square is `n` times its diagonal square ledger.
Consequently no cardinality-free synthesis estimate follows from diagonal
energy alone. -/
theorem identicalModes_coherentSynthesisGap (n : ℕ) :
    ‖∑ _ : Fin n, (1 : ℂ)‖ ^ 2 =
      (n : ℝ) * (∑ _ : Fin n, ‖(1 : ℂ)‖ ^ 2) := by
  rw [identicalModes_coherentSynthesisNormSq,
    identicalModes_analysisSquareLedger]
  ring

/-- The literal complex coefficient of the `n`th generator mode. -/
noncomputable def parameterizedPrimeEulerModeCoefficient
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) : ℂ :=
  -((alpha : ℂ) ^ n) *
    (ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)

theorem parameterizedPrimeEulerGeneratorMode_apply_eq_coefficient
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) (u : finiteSCarrier) :
    parameterizedPrimeEulerGeneratorMode alpha p n u =
      parameterizedPrimeEulerModeCoefficient alpha p n •
        cc20GlobalLogTranslation
          (-((n + 1 : ℕ) : ℝ) * Real.log p) u := by
  simpa [parameterizedPrimeEulerModeCoefficient] using
    parameterizedPrimeEulerGeneratorMode_apply alpha p n u

theorem normSq_parameterizedPrimeEulerModeCoefficient
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) :
    ‖parameterizedPrimeEulerModeCoefficient alpha p n‖ ^ 2 =
      alpha ^ (2 * n) *
        ccm24PrimeEulerCoefficient p ^ (2 * (n + 1)) := by
  unfold parameterizedPrimeEulerModeCoefficient
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]
  rw [mul_pow, ← abs_pow, sq_abs, ← pow_mul, ← pow_mul]
  simp only [Nat.mul_comm]

/-- Scalar square energy of the `n`th genuine generator mode.  Here `n=m-1`,
so the boundary displacement has length `m log p`. -/
noncomputable def parameterizedPrimeEulerModeBoundaryEnergy
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) : ℝ :=
  alpha ^ (2 * n) *
    ccm24PrimeEulerCoefficient p ^ (2 * (n + 1)) *
      ((n + 1 : ℕ) : ℝ) * Real.log p

theorem ccm24PrimeEulerCoefficient_sq (p : CCM24VisiblePrime) :
    ccm24PrimeEulerCoefficient p ^ 2 = ((p : ℝ)⁻¹) := by
  have hp : (0 : ℝ) ≤ p := by positivity
  rw [ccm24PrimeEulerCoefficient, div_pow, one_pow,
    Real.sq_sqrt hp]
  simp only [one_div]

theorem ccm24PrimeEulerCoefficient_even_pow
    (p : CCM24VisiblePrime) (m : ℕ) :
    ccm24PrimeEulerCoefficient p ^ (2 * m) = ((p : ℝ)⁻¹) ^ m := by
  rw [pow_mul, ccm24PrimeEulerCoefficient_sq]

theorem parameterizedPrimeEulerModeBoundaryEnergy_nonneg
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) :
    0 ≤ parameterizedPrimeEulerModeBoundaryEnergy alpha p n := by
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.le_of_lt p.property)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp
  have halpha : 0 ≤ alpha ^ (2 * n) := by
    rw [pow_mul]
    positivity
  have hcoefficient :
      0 ≤ ccm24PrimeEulerCoefficient p ^ (2 * (n + 1)) :=
    pow_nonneg (ccm24PrimeEulerCoefficient_nonneg p) _
  unfold parameterizedPrimeEulerModeBoundaryEnergy
  exact mul_nonneg
    (mul_nonneg (mul_nonneg halpha hcoefficient) (by positivity)) hlog

/-- Exact synchronized-time square ledger.  Squaring the mode coefficient
and integrating `alpha` converts the half-power Euler coefficient into the
summable full-power coefficient `p^(-m)`. -/
theorem integral_parameterizedPrimeEulerModeBoundaryEnergy
    (p : CCM24VisiblePrime) (n : ℕ) :
    (∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n) =
      ((n + 1 : ℕ) : ℝ) / (2 * n + 1 : ℕ) *
        Real.log p * ((p : ℝ)⁻¹) ^ (n + 1) := by
  unfold parameterizedPrimeEulerModeBoundaryEnergy
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_pow]
  rw [ccm24PrimeEulerCoefficient_even_pow]
  norm_num
  field_simp

/-- The exact factor `m/(2m-1)` is at most one, leaving the canonical
geometric square-energy majorant. -/
theorem integral_parameterizedPrimeEulerModeBoundaryEnergy_le
    (p : CCM24VisiblePrime) (n : ℕ) :
    (∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n) ≤
      Real.log p * ((p : ℝ)⁻¹) ^ (n + 1) := by
  rw [integral_parameterizedPrimeEulerModeBoundaryEnergy]
  have hlog : 0 ≤ Real.log p := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.le_of_lt p.property)
  have hpow : 0 ≤ ((p : ℝ)⁻¹) ^ (n + 1) := by positivity
  have hdenom : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
  have hratio : ((n + 1 : ℕ) : ℝ) / (2 * n + 1 : ℕ) ≤ 1 := by
    apply (div_le_one hdenom).2
    exact_mod_cast (show n + 1 ≤ 2 * n + 1 by omega)
  calc
    ((n + 1 : ℕ) : ℝ) / (2 * n + 1 : ℕ) *
          Real.log p * ((p : ℝ)⁻¹) ^ (n + 1) =
        (((n + 1 : ℕ) : ℝ) / (2 * n + 1 : ℕ)) *
          (Real.log p * ((p : ℝ)⁻¹) ^ (n + 1)) := by ring
    _ ≤ 1 * (Real.log p * ((p : ℝ)⁻¹) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg hlog hpow)
    _ = Real.log p * ((p : ℝ)⁻¹) ^ (n + 1) := by ring

/-- The geometric majorant for one integrated prime-power boundary mode. -/
noncomputable def primeEulerModeSquareMajorant
    (p : CCM24VisiblePrime) (n : ℕ) : ℝ :=
  Real.log p * ((p : ℝ)⁻¹) ^ (n + 1)

theorem primeEulerModeSquareMajorant_nonneg
    (p : CCM24VisiblePrime) (n : ℕ) :
    0 ≤ primeEulerModeSquareMajorant p n := by
  unfold primeEulerModeSquareMajorant
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.le_of_lt p.property)
  exact mul_nonneg (Real.log_nonneg hp) (by positivity)

theorem summable_primeEulerModeSquareMajorant
    (p : CCM24VisiblePrime) :
    Summable (primeEulerModeSquareMajorant p) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  have hq_nonneg : 0 ≤ ((p : ℝ)⁻¹) := by positivity
  have hq_lt : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp
  have hgeom : Summable (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one hq_nonneg hq_lt
  have hscaled := hgeom.mul_left (Real.log p * (p : ℝ)⁻¹)
  apply hscaled.congr
  intro n
  unfold primeEulerModeSquareMajorant
  rw [pow_succ]
  ring

theorem tsum_primeEulerModeSquareMajorant
    (p : CCM24VisiblePrime) :
    ∑' n : ℕ, primeEulerModeSquareMajorant p n =
      Real.log p / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property
  have hq_nonneg : 0 ≤ ((p : ℝ)⁻¹) := by positivity
  have hq_lt : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp
  calc
    ∑' n : ℕ, primeEulerModeSquareMajorant p n =
        ∑' n : ℕ,
          (Real.log p * (p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ n := by
      apply tsum_congr
      intro n
      unfold primeEulerModeSquareMajorant
      rw [pow_succ]
      ring
    _ = (Real.log p * (p : ℝ)⁻¹) *
        (∑' n : ℕ, ((p : ℝ)⁻¹) ^ n) := by rw [tsum_mul_left]
    _ = (Real.log p * (p : ℝ)⁻¹) *
        (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [tsum_geometric_of_lt_one hq_nonneg hq_lt]
    _ = Real.log p / ((p : ℝ) - 1) := by
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
      have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
      field_simp

/-- The complete `m >= 1` synchronized square energy is summable at one
visible prime. -/
theorem summable_integral_parameterizedPrimeEulerModeBoundaryEnergy
    (p : CCM24VisiblePrime) :
    Summable (fun n : ℕ =>
      ∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n) := by
  apply Summable.of_nonneg_of_le
  · intro n
    rw [integral_parameterizedPrimeEulerModeBoundaryEnergy]
    have hp : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.le_of_lt p.property)
    positivity
  · intro n
    exact integral_parameterizedPrimeEulerModeBoundaryEnergy_le p n
  · exact summable_primeEulerModeSquareMajorant p

theorem tsum_integral_parameterizedPrimeEulerModeBoundaryEnergy_le
    (p : CCM24VisiblePrime) :
    (∑' n : ℕ,
      ∫ alpha : ℝ in 0..1,
        parameterizedPrimeEulerModeBoundaryEnergy alpha p n) ≤
      Real.log p / ((p : ℝ) - 1) := by
  calc
    (∑' n : ℕ,
        ∫ alpha : ℝ in 0..1,
          parameterizedPrimeEulerModeBoundaryEnergy alpha p n) ≤
        ∑' n : ℕ, primeEulerModeSquareMajorant p n :=
      (summable_integral_parameterizedPrimeEulerModeBoundaryEnergy p).tsum_le_tsum
        (fun n => integral_parameterizedPrimeEulerModeBoundaryEnergy_le p n)
        (summable_primeEulerModeSquareMajorant p)
    _ = Real.log p / ((p : ℝ) - 1) :=
      tsum_primeEulerModeSquareMajorant p

/-- Sum the complete mode square budget over one finite visible-prime list.
The finite prime sum remains outside the convergent mode sums, matching the
actual generator construction. -/
theorem sum_tsum_integral_parameterizedPrimeEulerModeBoundaryEnergy_le
    (S : List CCM24VisiblePrime) :
    (S.map (fun p =>
      ∑' n : ℕ,
        ∫ alpha : ℝ in 0..1,
          parameterizedPrimeEulerModeBoundaryEnergy alpha p n)).sum ≤
      (S.map (fun (p : CCM24VisiblePrime) =>
        Real.log (p : ℝ) / ((p : ℝ) - 1))).sum := by
  induction S with
  | nil => simp
  | cons p S ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (tsum_integral_parameterizedPrimeEulerModeBoundaryEnergy_le p) ih

end CCM24FiniteSWeightedTranslationBessel
end CCM25Concrete
end Source
end ConnesWeilRH
