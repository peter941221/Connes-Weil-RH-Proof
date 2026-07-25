/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar

/-!
# Literal readback constructor for the actual Julia Schur input

Proof 544 generates the Schur transfer contract. This module removes the
remaining readback bookkeeping when the range-sine row is defined literally
as the chosen physical readout applied to the actual graph sine.

The only analytic input left for such a step is the weighted range-sine
estimate. No estimate, Gate 3U conclusion, or sign theorem is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualJuliaReadbackConstructor

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSProjectionTrace

/-- The literal physical range-sine row attached to one suffix Schur step. -/
noncomputable def suffixLiteralSchurFrameRangeSine
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (readout : finiteSCarrier →L[ℂ] G) :
    finiteSCarrier →L[ℂ] G :=
  readout ∘L
    (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
      (by norm_num) p).toColligation.graphSine
      (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
        (by norm_num) p).toColligation.graphCosine

/-- Build a suffix Schur-frame step with the 544 generated transfer contract
and definitional graph-sine readback. -/
noncomputable def suffixSchurFrameStepDataOfLiteralReadback
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (rangeSine_weighted_le : ∀ x : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).normalizedSchurFrame
          (parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract
            lambda 1 S (by norm_num) p) x‖ ^ 2) :
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S :=
  SuffixPrimeEulerProjectedJuliaSchurFrameStepData.ofGeneratedContract
    (rangeSine := suffixLiteralSchurFrameRangeSine lambda p S readout)
    fixedSourceReadout readout rangeSine_weighted_le rfl

@[simp]
theorem suffixSchurFrameStepDataOfLiteralReadback_rangeSine
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (rangeSine_weighted_le : ∀ x : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).normalizedSchurFrame
          (parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract
            lambda 1 S (by norm_num) p) x‖ ^ 2) :
    (suffixSchurFrameStepDataOfLiteralReadback
      fixedSourceReadout readout rangeSine_weighted_le).rangeSine =
      suffixLiteralSchurFrameRangeSine lambda p S readout :=
  rfl

/-- The finite-S graph-sine readback is now definitional for the literal
constructor. -/
theorem suffixSchurFrameStepDataOfLiteralReadback_rangeSine_readback
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (rangeSine_weighted_le : ∀ x : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).normalizedSchurFrame
          (parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract
            lambda 1 S (by norm_num) p) x‖ ^ 2) :
    (suffixSchurFrameStepDataOfLiteralReadback
      fixedSourceReadout readout rangeSine_weighted_le).rangeSine =
      readout ∘L
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
          (by norm_num) p).toColligation.graphSine
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).toColligation.graphCosine :=
  rfl

/-- The fixed-source readback is the same literal equality after the actual
polar frame is inserted. -/
theorem suffixSchurFrameStepDataOfLiteralReadback_fixedSource_readback
    {lambda : CCM24SoninScale} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (fixedSourceReadout : G →L[ℂ] G)
    (readout : finiteSCarrier →L[ℂ] G)
    (rangeSine_weighted_le : ∀ x : finiteSCarrier,
      primeJuliaWeight p *
          ‖suffixLiteralSchurFrameRangeSine lambda p S readout x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).normalizedSchurFrame
          (parameterizedPrimeEulerProjectedJuliaInput_normalizedSchurFrame_contract
            lambda 1 S (by norm_num) p) x‖ ^ 2) :
    (suffixSchurFrameStepDataOfLiteralReadback
        fixedSourceReadout readout rangeSine_weighted_le).rangeSine ∘L
        parameterizedSoninPolarFrame lambda 1 S (by norm_num) =
      readout ∘L
        (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
          (by norm_num) p).toColligation.graphSine
          (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
            (by norm_num) p).toColligation.graphCosine ∘L
        parameterizedSoninPolarFrame lambda 1 S (by norm_num) := by
  simpa only [suffixSchurFrameStepDataOfLiteralReadback]
    using
      (SuffixPrimeEulerProjectedJuliaSchurFrameStepData.fixedSource_rangeSine_readback
        (suffixSchurFrameStepDataOfLiteralReadback
          fixedSourceReadout readout rangeSine_weighted_le))

end CCM24FiniteSActualJuliaReadbackConstructor
end CCM25Concrete
end Source
end ConnesWeilRH
