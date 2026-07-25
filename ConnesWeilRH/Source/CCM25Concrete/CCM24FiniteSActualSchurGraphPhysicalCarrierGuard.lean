/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadback

/-!
# Graph-cascade carrier guard

The graph physical cascade and the source-owned Julia range readout are
different data paths.  The graph product does not inspect `stepData`, while
`fixedSourceReadout` is an independent field of the source step record.  This
module records both facts so that no later theorem can infer a physical Julia
readout from the graph product alone.

No factorization, norm estimate, sign, Gate 3U result, or RH conclusion is
asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurGraphPhysicalCarrierGuard

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSActualSchurGraphPhysicalBoundaryTargetReadback
open CCM24FiniteSActualSchurGraphPhysicalCascadeResidual
open CCM24FiniteSActualSchurGraphPhysicalEndpointReadback

/-! ## The independent fixed-source readout field -/

/-- Replace only the fixed-source readout of a source-owned step record. -/
noncomputable def withFixedSourceReadout
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (fixedSourceReadout : G →L[ℂ] G) :
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S :=
  { data with fixedSourceReadout := fixedSourceReadout }

@[simp]
theorem withFixedSourceReadout_fixedSourceReadout
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (fixedSourceReadout : G →L[ℂ] G) :
    (withFixedSourceReadout lambda data fixedSourceReadout).fixedSourceReadout =
      fixedSourceReadout :=
  rfl

@[simp]
theorem withFixedSourceReadout_rangeSine
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (fixedSourceReadout : G →L[ℂ] G) :
    (withFixedSourceReadout lambda data fixedSourceReadout).rangeSine =
      data.rangeSine :=
  rfl

@[simp]
theorem withFixedSourceReadout_readout
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (fixedSourceReadout : G →L[ℂ] G) :
    (withFixedSourceReadout lambda data fixedSourceReadout).readout =
      data.readout :=
  rfl

@[simp]
theorem withFixedSourceReadout_transfer_contract
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    (data : SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (fixedSourceReadout : G →L[ℂ] G) :
    (withFixedSourceReadout lambda data fixedSourceReadout).transfer_contract =
      data.transfer_contract :=
  rfl

/-! ## The graph product ignores the Julia range data -/

theorem suffixActualSchurGraphPhysicalProduct_eq_of_stepData
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    suffixActualSchurGraphPhysicalProduct lambda stepData₁ S =
      suffixActualSchurGraphPhysicalProduct lambda stepData₂ S := by
  induction S with
  | nil => rfl
  | cons p S ih =>
      simp only [suffixActualSchurGraphPhysicalProduct]
      rw [ih]

theorem sourceActualBandGraphPhysicalCoframe_eq_of_stepData
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    sourceActualBandGraphPhysicalCoframe lambda stepData₁ S =
      sourceActualBandGraphPhysicalCoframe lambda stepData₂ S := by
  unfold sourceActualBandGraphPhysicalCoframe
  rw [suffixActualSchurGraphPhysicalProduct_eq_of_stepData
    lambda stepData₁ stepData₂ S]

theorem sourceActualBandGraphPhysicalEndpointCoframe_eq_of_stepData
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalEndpointCoframe lambda stepData₁ family =
      sourceActualBandGraphPhysicalEndpointCoframe lambda stepData₂ family := by
  unfold sourceActualBandGraphPhysicalEndpointCoframe
  rw [sourceActualBandGraphPhysicalCoframe_eq_of_stepData
    lambda stepData₁ stepData₂ family.visiblePrimes]

/-! ## The boundary target is equally independent -/

theorem sourceActualBandGraphPhysicalBoundaryDaggerTarget_eq_of_stepData
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily)
    (survivor : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
    sourceActualBandGraphPhysicalBoundaryDaggerTarget rightLeg lambda
        stepData₁ family survivor =
      sourceActualBandGraphPhysicalBoundaryDaggerTarget rightLeg lambda
        stepData₂ family survivor := by
  rw [sourceActualBandGraphPhysicalBoundaryDaggerTarget,
    sourceActualBandGraphPhysicalBoundaryDaggerTarget,
    sourceActualBandGraphPhysicalEndpointCoframe_eq_of_stepData
      lambda stepData₁ stepData₂ family]

theorem sourceActualBandGraphPhysicalEndpointResidual_eq_of_stepData
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (lambda : CCM24SoninScale)
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalEndpointResidual lambda stepData₁ family =
      sourceActualBandGraphPhysicalEndpointResidual lambda stepData₂ family := by
  unfold sourceActualBandGraphPhysicalEndpointResidual
  rw [sourceActualBandGraphPhysicalEndpointCoframe_eq_of_stepData
    lambda stepData₁ stepData₂ family]

theorem sourceActualBandGraphPhysicalBoundaryDaggerResidual_eq_of_stepData
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (lambda : CCM24SoninScale)
    (stepData₁ stepData₂ : ∀ (p : CCM24VisiblePrime)
      (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (family : FinitePrimePowerFamily) :
    sourceActualBandGraphPhysicalBoundaryDaggerResidual rightLeg lambda
        stepData₁ family =
      sourceActualBandGraphPhysicalBoundaryDaggerResidual rightLeg lambda
        stepData₂ family := by
  unfold sourceActualBandGraphPhysicalBoundaryDaggerResidual
  rw [sourceActualBandGraphPhysicalEndpointResidual_eq_of_stepData
    lambda stepData₁ stepData₂ family]

end CCM24FiniteSActualSchurGraphPhysicalCarrierGuard
end CCM25Concrete
end Source
end ConnesWeilRH
