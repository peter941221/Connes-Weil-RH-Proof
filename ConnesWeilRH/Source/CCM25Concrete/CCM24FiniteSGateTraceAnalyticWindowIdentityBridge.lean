/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridge

/-!
# Gate trace handoff from analytic windows, identity-input form

This module feeds the Proof 712 completed endpoint readout into the Proof 697
Gate-facing trace-norm handoff.  The bridge is deliberately identity-input:
after Proof 712 removes the common source input from the endpoint readout, the
remaining completed-history energy premise becomes the Hilbert-basis energy
of the identity input.  That premise is explicit and is not proved here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGateTraceAnalyticWindowIdentityBridge

open MeasureTheory
open scoped FourierTransform InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridge
open CCM24FiniteSCompletedPhysicalTerminalReadout
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSGramResponse
open CCM24FiniteSJuliaBessel
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Trace handoff -/

private abbrev completedHistoryTraceNormBound :=
  lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_completedHistory_of_norm_le

set_option maxHeartbeats 4000000 in
-- This theorem combines the long completed endpoint tuple from Proof 712 with
-- the Gate-facing completed-history handoff from Proof 697.
theorem lowerFactorGauged_trace_norm_le_of_analytic_window_originalMultiplier_idInput
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c)
    {ι κ τ ιr κr τr ν mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (inclusion : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (survivor : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (data : PhysicalBoundaryDaggerReadoutContract
      (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      (physicalBoundaryDaggerTarget
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (sourceActualBandForwardEndpointCoframe lambda family)
        inclusion survivor))
    (terminalReadout : sourceSoninCarrier lambda →L[ℂ]
      commonBoundaryCarrier a c)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hinputId : Summable fun i => ‖(sourceBasis i :
      sourceSoninCarrier lambda)‖ ^ 2)
    (hscaledInputEnergy :
      bound ^ 2 * (∑' i, ‖(sourceBasis i :
          sourceSoninCarrier lambda)‖ ^ 2) ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis)
    (hterminal :
      terminalReadout ∘L
          juliaSurvivor
            ((suffixActualSchurFrameSteps lambda stepData family.visiblePrimes).map
              (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
            fixedPhysicalSourceInput owner lambda a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor =
        ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
            ∘L inclusion ∘L survivor) ∘L
          fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            boundaryBasis sourceBasis hfactor)
    (hjoint :
      ‖completedRectangularBoundaryReadoutOfComponents
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
          terminalReadout data.readout‖ ≤ bound)
    (hfourier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  obtain ⟨readout, hreadout, hendpoint⟩ :=
    exists_completed_readout_of_analytic_window_originalMultiplier
      owner lambda a c hac hsupp hwidth negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
      (steps := suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
      (rightLeg :=
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right)
      (endpoint := sourceActualBandForwardEndpointCoframe lambda family)
      (inclusion := inclusion) (survivor := survivor)
      data terminalReadout bound hterminal hjoint hfourier hanalyticRep
  have hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            (1 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) := by
    rw [hendpoint]
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  exact
    completedHistoryTraceNormBound
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor stepData
      (1 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
      hinputId bound hbound hscaledInputEnergy readout hreadout hphysical

end CCM24FiniteSGateTraceAnalyticWindowIdentityBridge
end CCM25Concrete
end Source
end ConnesWeilRH
