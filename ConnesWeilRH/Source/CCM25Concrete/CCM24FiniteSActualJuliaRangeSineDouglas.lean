/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaReadbackConstructor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor

/-!
# Douglas owner for the actual Julia range-sine row

Proof 544 generates the Schur transfer contract, and Proof 546 makes the
graph-sine readback definitional when the range row is chosen literally.  The
remaining field is the weighted range-sine estimate.  This module identifies
that estimate with a norm-one Douglas factor through the actual canonical
Julia defect of the normalized Schur frame.

This is an ownership and obstruction result only.  It does not construct the
source-specific factor, prove Gate 3U, prove the finite-S sign, or prove RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaRangeSineDouglas

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualJuliaReadbackConstructor
open CCM24FiniteSDouglasFactor
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSProjectionTrace

open scoped InnerProduct

theorem primeJuliaWeight_pos (p : CCM24VisiblePrime) :
    0 < primeJuliaWeight p := by
  unfold primeJuliaWeight
  have hp : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.property
  linarith

/-- The actual canonical Julia defect for one synchronized suffix Schur slice. -/
noncomputable def suffixCanonicalJuliaDefect
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  canonicalJuliaDefect
    (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
      (by norm_num) p).normalizedSchurFrame
    (parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract
      lambda 1 S (by norm_num) p)

/-- The weighted range-sine row whose square is the stored weighted energy. -/
noncomputable def suffixWeightedRangeSineMap
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (p : CCM24VisiblePrime) (rangeSine : finiteSCarrier →L[ℂ] G) :
    finiteSCarrier →L[ℂ] G :=
  (Real.sqrt (primeJuliaWeight p) : ℂ) • rangeSine

theorem suffixWeightedRangeSineMap_normSq
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (p : CCM24VisiblePrime) (rangeSine : finiteSCarrier →L[ℂ] G)
    (x : finiteSCarrier) :
    ‖suffixWeightedRangeSineMap p rangeSine x‖ ^ 2 =
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 := by
  unfold suffixWeightedRangeSineMap
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (primeJuliaWeight_nonneg p)]

/--
The weighted range-sine estimate is exactly a norm-one Douglas factor through
the actual canonical defect.
-/
theorem exists_weightedRangeSineFactor_of_rangeSine_weighted_le
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (rangeSine : finiteSCarrier →L[ℂ] G)
    (hweighted : ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2) :
    ∃ factor : finiteSCarrier →L[ℂ] G,
      ‖factor‖ ≤ 1 ∧
        factor ∘L suffixCanonicalJuliaDefect lambda p S =
          suffixWeightedRangeSineMap p rangeSine := by
  let A := suffixWeightedRangeSineMap p rangeSine
  let B := suffixCanonicalJuliaDefect lambda p S
  have hdom : ∀ x : finiteSCarrier,
      ‖A x‖ ^ 2 ≤ (1 : ℝ) ^ 2 * ‖B x‖ ^ 2 := by
    intro x
    calc
      ‖A x‖ ^ 2 = primeJuliaWeight p * ‖rangeSine x‖ ^ 2 := by
        simpa only [A] using
          suffixWeightedRangeSineMap_normSq p rangeSine x
      _ ≤ ‖B x‖ ^ 2 := by
        simpa only [B] using hweighted x
      _ = (1 : ℝ) ^ 2 * ‖B x‖ ^ 2 := by ring
  simpa only [A, B] using
    exists_factor_of_norm_sq_le A B 1 (by norm_num) hdom

/--
Conversely, a norm-one Douglas factor through the canonical defect is exactly
the weighted range-sine estimate.
-/
theorem rangeSine_weighted_le_of_weightedRangeSineFactor
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (rangeSine : finiteSCarrier →L[ℂ] G)
    (factor : finiteSCarrier →L[ℂ] G)
    (hfactor_norm : ‖factor‖ ≤ 1)
    (hfactor :
      factor ∘L suffixCanonicalJuliaDefect lambda p S =
        suffixWeightedRangeSineMap p rangeSine) :
    ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2 := by
  intro x
  let A := suffixWeightedRangeSineMap p rangeSine
  let B := suffixCanonicalJuliaDefect lambda p S
  have hpoint : A x = factor (B x) := by
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] G => T x) hfactor
    simpa only [A, B, ContinuousLinearMap.comp_apply] using h.symm
  have hfactor_point : ‖factor (B x)‖ ≤ ‖B x‖ := by
    calc
      ‖factor (B x)‖ ≤ ‖factor‖ * ‖B x‖ := factor.le_opNorm _
      _ ≤ 1 * ‖B x‖ := by
        exact mul_le_mul_of_nonneg_right hfactor_norm (norm_nonneg _)
      _ = ‖B x‖ := one_mul _
  have hfactor_sq : ‖factor (B x)‖ ^ 2 ≤ ‖B x‖ ^ 2 := by
    nlinarith [norm_nonneg (factor (B x)), norm_nonneg (B x)]
  calc
    primeJuliaWeight p * ‖rangeSine x‖ ^ 2 = ‖A x‖ ^ 2 := by
      exact (suffixWeightedRangeSineMap_normSq p rangeSine x).symm
    _ = ‖factor (B x)‖ ^ 2 := by rw [hpoint]
    _ ≤ ‖B x‖ ^ 2 := hfactor_sq

theorem rangeSine_weighted_le_iff_exists_weightedRangeSineFactor
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (rangeSine : finiteSCarrier →L[ℂ] G) :
    (∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2) ↔
      ∃ factor : finiteSCarrier →L[ℂ] G,
        ‖factor‖ ≤ 1 ∧
          factor ∘L suffixCanonicalJuliaDefect lambda p S =
            suffixWeightedRangeSineMap p rangeSine := by
  constructor
  · exact exists_weightedRangeSineFactor_of_rangeSine_weighted_le rangeSine
  · rintro ⟨factor, hfactor_norm, hfactor⟩
    exact rangeSine_weighted_le_of_weightedRangeSineFactor
      rangeSine factor hfactor_norm hfactor

theorem SuffixPrimeEulerProjectedJuliaSchurFrameStepData.exists_weightedRangeSineFactor
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    ∃ factor : finiteSCarrier →L[ℂ] G,
      ‖factor‖ ≤ 1 ∧
        factor ∘L suffixCanonicalJuliaDefect lambda p S =
          suffixWeightedRangeSineMap p data.rangeSine := by
  exact exists_weightedRangeSineFactor_of_rangeSine_weighted_le
    data.rangeSine data.rangeSine_weighted_le

/--
Any valid weighted range-sine estimate must annihilate the kernel of the
actual canonical defect.
-/
theorem rangeSine_eq_zero_of_rangeSine_weighted_le_of_canonical_defect_eq_zero
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (rangeSine : finiteSCarrier →L[ℂ] G)
    (hweighted : ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2)
    {x : finiteSCarrier}
    (hdefect : suffixCanonicalJuliaDefect lambda p S x = 0) :
    rangeSine x = 0 := by
  have hleSq : primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤ (0 : ℝ) ^ 2 := by
    simpa only [hdefect, norm_zero] using hweighted x
  have hle : primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤ 0 := by
    simpa using hleSq
  have hnonneg : 0 ≤ primeJuliaWeight p * ‖rangeSine x‖ ^ 2 := by
    exact mul_nonneg (primeJuliaWeight_nonneg p) (sq_nonneg _)
  have hmul : primeJuliaWeight p * ‖rangeSine x‖ ^ 2 = 0 :=
    le_antisymm hle hnonneg
  have hweight_ne : primeJuliaWeight p ≠ 0 :=
    ne_of_gt (primeJuliaWeight_pos p)
  have hnormSq : ‖rangeSine x‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hweight_ne
  have hnorm : ‖rangeSine x‖ = 0 := by
    nlinarith [norm_nonneg (rangeSine x)]
  exact norm_eq_zero.mp hnorm

theorem SuffixPrimeEulerProjectedJuliaSchurFrameStepData.rangeSine_eq_zero_of_defect
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    {x : finiteSCarrier}
    (hdefect : suffixCanonicalJuliaDefect lambda p S x = 0) :
    data.rangeSine x = 0 :=
  rangeSine_eq_zero_of_rangeSine_weighted_le_of_canonical_defect_eq_zero
    data.rangeSine data.rangeSine_weighted_le hdefect

/-- A nonzero range-sine value on the canonical-defect kernel rules out the
weighted estimate for that proposed row. -/
theorem not_rangeSine_weighted_le_of_canonical_defect_eq_zero_of_rangeSine_ne_zero
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (rangeSine : finiteSCarrier →L[ℂ] G)
    {x : finiteSCarrier}
    (hdefect : suffixCanonicalJuliaDefect lambda p S x = 0)
    (hrange : rangeSine x ≠ 0) :
    ¬ ∀ y : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine y‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S y‖ ^ 2 := by
  intro hweighted
  exact hrange
    (rangeSine_eq_zero_of_rangeSine_weighted_le_of_canonical_defect_eq_zero
      rangeSine hweighted hdefect)

/--
For the literal readback constructor, the same obstruction says: if the chosen
physical readout sees a canonical-defect zero mode through graph-sine, then
the remaining weighted estimate cannot be supplied.
-/
theorem not_literalRangeSine_weighted_le_of_defect_zero_of_readout_ne_zero
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (readout : finiteSCarrier →L[ℂ] G)
    {x : finiteSCarrier}
    (hdefect : suffixCanonicalJuliaDefect lambda p S x = 0)
    (hreadout :
      suffixLiteralSchurFrameRangeSine lambda p S readout x ≠ 0) :
    ¬ ∀ y : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout y‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S y‖ ^ 2 := by
  exact
    not_rangeSine_weighted_le_of_canonical_defect_eq_zero_of_rangeSine_ne_zero
      (suffixLiteralSchurFrameRangeSine lambda p S readout)
      hdefect hreadout

end CCM24FiniteSActualJuliaRangeSineDouglas
end CCM25Concrete
end Source
end ConnesWeilRH
