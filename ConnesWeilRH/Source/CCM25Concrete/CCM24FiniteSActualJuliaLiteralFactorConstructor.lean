/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaRangeSineDouglas

/-!
# Literal Julia range-sine factor constructor

Proof 550 identifies the remaining weighted range-sine estimate with a
Douglas factor through the actual canonical Schur defect. This module
packages the source-facing version needed by the literal Proof 546 readback
constructor: a factor for the weighted literal graph-sine row is exactly the
data needed to build the actual suffix Schur-frame step.

This is still a producer interface, not the missing source estimate. It does
not construct the factor, close Gate 3U, prove the finite-S sign, or prove RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaLiteralFactorConstructor

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualJuliaRangeSineDouglas
open CCM24FiniteSActualJuliaReadbackConstructor
open CCM24FiniteSJuliaCausal
open CCM24FiniteSProjectionTrace

/-! ## Literal factor package -/

/-- A concrete Douglas factor for the literal physical range-sine row. -/
structure SuffixLiteralRangeSineFactorData
    (lambda : CCM24SoninScale) (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G) where
  factor : finiteSCarrier →L[ℂ] G
  factor_norm_le_one : ‖factor‖ ≤ 1
  factorization :
    factor ∘L suffixCanonicalJuliaDefect lambda p S =
      suffixWeightedRangeSineMap p
        (suffixLiteralSchurFrameRangeSine lambda p S readout)

/-- A literal factor supplies the weighted range-sine estimate required by
the actual Schur-frame step constructor. -/
theorem SuffixLiteralRangeSineFactorData.rangeSine_weighted_le
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    ∀ x : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
        ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2 :=
  rangeSine_weighted_le_of_weightedRangeSineFactor
    (suffixLiteralSchurFrameRangeSine lambda p S readout)
    data.factor data.factor_norm_le_one data.factorization

/-- Consume the literal factor and build the actual suffix Schur-frame step. -/
noncomputable def SuffixLiteralRangeSineFactorData.toStepData
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S :=
  suffixSchurFrameStepDataOfLiteralReadback
    fixedSourceReadout readout data.rangeSine_weighted_le

@[simp]
theorem SuffixLiteralRangeSineFactorData.toStepData_rangeSine
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    data.toStepData.rangeSine =
      suffixLiteralSchurFrameRangeSine lambda p S readout :=
  rfl

@[simp]
theorem SuffixLiteralRangeSineFactorData.toStepData_fixedSourceReadout
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    data.toStepData.fixedSourceReadout = fixedSourceReadout :=
  rfl

@[simp]
theorem SuffixLiteralRangeSineFactorData.toStepData_readout
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    data.toStepData.readout = readout :=
  rfl

/-- The generated step has the intended literal graph-sine readback. -/
theorem SuffixLiteralRangeSineFactorData.toStepData_rangeSine_readback
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {fixedSourceReadout : G →L[ℂ] G}
    {readout : finiteSCarrier →L[ℂ] G}
    (data :
      SuffixLiteralRangeSineFactorData
        lambda G p S fixedSourceReadout readout) :
    data.toStepData.rangeSine =
      readout ∘L
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
          (by norm_num) p).toColligation.graphSine
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).toColligation.graphCosine :=
  rfl

/-! ## Exact source obligation -/

/-- For a fixed literal readout, the factor package is exactly the weighted
range-sine estimate. -/
theorem exists_literalRangeSineFactor_iff_rangeSine_weighted_le
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    Nonempty
        (SuffixLiteralRangeSineFactorData
          lambda G p S fixedSourceReadout readout) ↔
      ∀ x : finiteSCarrier,
        primeJuliaWeight p *
            ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
          ‖suffixCanonicalJuliaDefect lambda p S x‖ ^ 2 := by
  constructor
  · rintro ⟨data⟩
    exact data.rangeSine_weighted_le
  · intro hweighted
    rcases
      exists_weightedRangeSineFactor_of_rangeSine_weighted_le
        (suffixLiteralSchurFrameRangeSine lambda p S readout)
        hweighted with
      ⟨factor, hfactor_norm, hfactor⟩
    exact ⟨
      { factor := factor
        factor_norm_le_one := hfactor_norm
        factorization := hfactor }⟩

/-- Equivalently, the literal factor package is exactly what is needed to
build a literal suffix Schur-frame step with those readout fields. -/
theorem exists_literalRangeSineFactor_iff_exists_literalStepData
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    Nonempty
        (SuffixLiteralRangeSineFactorData
          lambda G p S fixedSourceReadout readout) ↔
      ∃ data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S,
        data.fixedSourceReadout = fixedSourceReadout ∧
          data.readout = readout ∧
          data.rangeSine =
            suffixLiteralSchurFrameRangeSine lambda p S readout := by
  constructor
  · rintro ⟨factorData⟩
    refine ⟨factorData.toStepData, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
  · rintro ⟨data, hfixed, hreadout, hrange⟩
    rcases
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData.exists_weightedRangeSineFactor
        data with
      ⟨factor, hfactor_norm, hfactor⟩
    have hfactor' :
        factor ∘L suffixCanonicalJuliaDefect lambda p S =
          suffixWeightedRangeSineMap p
            (suffixLiteralSchurFrameRangeSine lambda p S readout) := by
      simpa only [hrange] using hfactor
    exact ⟨
      { factor := factor
        factor_norm_le_one := hfactor_norm
        factorization := hfactor' }⟩

/-! ## Literal zero-mode obstruction -/

/-- A nonzero literal physical readout on the canonical-defect kernel rules
out the literal factor package. -/
theorem not_literalRangeSineFactor_of_defect_zero_of_readout_ne_zero
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    {x : finiteSCarrier}
    (hdefect : suffixCanonicalJuliaDefect lambda p S x = 0)
    (hreadout :
      suffixLiteralSchurFrameRangeSine lambda p S readout x ≠ 0) :
    ¬ Nonempty
        (SuffixLiteralRangeSineFactorData
          lambda G p S fixedSourceReadout readout) := by
  intro hdata
  have hweighted :=
    (exists_literalRangeSineFactor_iff_rangeSine_weighted_le
      fixedSourceReadout readout p S).mp hdata
  exact
    not_literalRangeSine_weighted_le_of_defect_zero_of_readout_ne_zero
      readout hdefect hreadout hweighted

end CCM24FiniteSActualJuliaLiteralFactorConstructor
end CCM25Concrete
end Source
end ConnesWeilRH
