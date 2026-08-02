/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInput

/-!
# Composed completed-history energy

The analytic-window bridge supplies an uncomposed readout identity:

```text
rightLeg o endpoint = readout o completedColumn.
```

The valid Hilbert--Schmidt consequence is obtained by composing both sides
with the actual source input.  This file records that consequence with a
separate energy definition.  It does not identify this composed energy with
the original Gate energy, whose endpoint is evaluated on the source basis
itself.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalHistoryComposition

open MeasureTheory
open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSJuliaBessel
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSFixedPhysicalSourceInput

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The correctly composed energy -/

/-- The combined physical right energy after an explicit source input has
been applied.  The input is part of the definition, so an uncomposed endpoint
readout can be composed legally before the basis sum is estimated. -/
noncomputable def sourceActualBandCombinedPhysicalRightEnergy_comp
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (sourceInput : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
    ℝ :=
  ∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
      (sourceActualBandForwardEndpointCoframe lambda family
        (sourceInput (sourceBasis i)))‖ ^ 2

set_option maxHeartbeats 4000000 in
-- The dependent completed-history carrier tuple needs a larger elaboration budget.
/-- An uncomposed completed-history readout controls the endpoint only after
the same source input is composed on both sides. -/
theorem
    sourceActualBandCombinedPhysicalRightEnergy_comp_le_of_completedActualSchurReadout_of_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (sourceInput : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖sourceInput (sourceBasis i)‖ ^ 2)
    (readout : completedRectangularBoundaryCarrier
      (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) →L[ℂ]
        commonBoundaryCarrier a c)
    (bound : ℝ) (hbound : 0 ≤ bound) (hreadout : ‖readout‖ ≤ bound)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)) :
    sourceActualBandCombinedPhysicalRightEnergy_comp owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor sourceInput ≤
      bound ^ 2 * (∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2) := by
  have henergy := completedRectangularBoundaryReadout_tsum_normSq_le_of_norm_le
    (steps := suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
    sourceBasis sourceInput hinput readout bound hbound hreadout
  have hphysicalApply : ∀ i,
      (readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) (sourceBasis i) =
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          (sourceActualBandForwardEndpointCoframe lambda family
            (sourceInput (sourceBasis i))) := by
    intro i
    have happ := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
          commonBoundaryCarrier a c => operator (sourceInput (sourceBasis i)))
      hphysical.symm
    simpa only [ContinuousLinearMap.comp_apply] using happ
  rw [sourceActualBandCombinedPhysicalRightEnergy_comp]
  calc
    (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (sourceActualBandForwardEndpointCoframe lambda family
          (sourceInput (sourceBasis i)))‖ ^ 2) =
        ∑' i, ‖(readout ∘L completedRectangularBoundaryColumn
            (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
              sourceInput) (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [hphysicalApply i]
    _ ≤ bound ^ 2 * (∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2) := henergy

set_option maxHeartbeats 4000000 in
-- The fixed physical source input and completed-history carrier are dependent.
/-- The fixed physical source input turns the composed-history estimate into
the explicit `2 * M` budget.  This is still an input-composed energy, not the
original Gate energy on the unmodified source basis. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_comp_fixedPhysicalSourceInput_le_twoMajorant
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (readout : completedRectangularBoundaryCarrier
      (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) →L[ℂ]
        commonBoundaryCarrier a c)
    (hreadout : ‖readout‖ ≤ 1)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)) :
    sourceActualBandCombinedPhysicalRightEnergy_comp owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor
        (fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor) ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  have hinput := fixedPhysicalSourceInput_summable_normSq
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have henergy :=
    sourceActualBandCombinedPhysicalRightEnergy_comp_le_of_completedActualSchurReadout_of_norm_le
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor stepData
      (fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor)
      hinput readout 1 (by norm_num) hreadout hphysical
  calc
    sourceActualBandCombinedPhysicalRightEnergy_comp owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor
        (fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor) ≤
        (1 : ℝ) ^ 2 *
          (∑' i, ‖fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis hfactor (sourceBasis i)‖ ^ 2) := henergy
    _ = ∑' i, ‖fixedPhysicalSourceInput owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis hfactor (sourceBasis i)‖ ^ 2 := by norm_num
    _ ≤ 2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis :=
      fixedPhysicalSourceInput_basisEnergy_le owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor

end CCM24FiniteSCompletedPhysicalHistoryComposition
end CCM25Concrete
end Source
end ConnesWeilRH
