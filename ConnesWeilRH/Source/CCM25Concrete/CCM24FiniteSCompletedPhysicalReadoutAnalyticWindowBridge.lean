/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalTerminalReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridge

/-!
# Completed physical readout from translated analytic windows

This module feeds the Proof 711 fixed physical source dense-range bridge into
the Proof 698 completed-history cancellation consumer.  The analytic-window
and Fourier/root nondegeneracy facts remain explicit source inputs.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridge

open MeasureTheory
open scoped FourierTransform InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSCompletedPhysicalTerminalReadout
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSFixedPhysicalSourceInputAnalyticWindowBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSJuliaBessel
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Completed readout consumers -/

set_option maxHeartbeats 4000000 in
-- The statement elaborates both the fixed physical source input and the
-- completed-history endpoint tuple from Proof 698.
theorem exists_completed_readout_of_analytic_window_originalMultiplier
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
        (sourceSoninCarrier lambda) K))
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (endpoint inclusion : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (survivor : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (data : PhysicalBoundaryDaggerReadoutContract steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      (physicalBoundaryDaggerTarget rightLeg endpoint inclusion survivor))
    (terminalReadout : sourceSoninCarrier lambda →L[ℂ] G)
    (bound : ℝ)
    (hterminal :
      terminalReadout ∘L
          juliaSurvivor (steps.map
            (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
            fixedPhysicalSourceInput owner lambda a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor =
        (rightLeg ∘L inclusion ∘L survivor) ∘L
          fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            boundaryBasis sourceBasis hfactor)
    (hjoint :
      ‖completedRectangularBoundaryReadoutOfComponents steps terminalReadout
          data.readout‖ ≤ bound)
    (hfourier : ∀ᵐ ξ ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) ξ ≠ 0)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∃ readout : completedRectangularBoundaryCarrier steps →L[ℂ] G,
      ‖readout‖ ≤ bound ∧
        rightLeg ∘L endpoint =
          readout ∘L completedRectangularBoundaryColumn steps := by
  exact
    PhysicalBoundaryDaggerReadoutContract.exists_completed_readout_of_physicalTarget_of_denseRange
      steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      rightLeg endpoint inclusion survivor data terminalReadout bound
      hterminal hjoint
      (fixedPhysicalSourceInput_denseRange_of_analytic_window_originalMultiplier
        owner lambda a c hac hsupp hwidth negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
        hfourier hanalyticRep)

set_option maxHeartbeats 4000000 in
-- The statement elaborates both the fixed physical source input and the
-- completed-history endpoint tuple from Proof 698.
theorem exists_completed_readout_of_analytic_window_finitePrimeTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0)
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
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
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
        (sourceSoninCarrier lambda) K))
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (endpoint inclusion : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (survivor : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (data : PhysicalBoundaryDaggerReadoutContract steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      (physicalBoundaryDaggerTarget rightLeg endpoint inclusion survivor))
    (terminalReadout : sourceSoninCarrier lambda →L[ℂ] G)
    (bound : ℝ)
    (hterminal :
      terminalReadout ∘L
          juliaSurvivor (steps.map
            (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
            fixedPhysicalSourceInput owner lambda a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor =
        (rightLeg ∘L inclusion ∘L survivor) ∘L
          fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            boundaryBasis sourceBasis hfactor)
    (hjoint :
      ‖completedRectangularBoundaryReadoutOfComponents steps terminalReadout
          data.readout‖ ≤ bound)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∃ readout : completedRectangularBoundaryCarrier steps →L[ℂ] G,
      ‖readout‖ ≤ bound ∧
        rightLeg ∘L endpoint =
          readout ∘L completedRectangularBoundaryColumn steps := by
  exact
    PhysicalBoundaryDaggerReadoutContract.exists_completed_readout_of_physicalTarget_of_denseRange
      steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      rightLeg endpoint inclusion survivor data terminalReadout bound
      hterminal hjoint
      (fixedPhysicalSourceInput_denseRange_of_analytic_window_finitePrimeTerm
        owner lambda a c hac hsupp hwidth hterm hfourierAnalytic
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor hanalyticRep)

set_option maxHeartbeats 4000000 in
-- The statement elaborates both the fixed physical source input and the
-- completed-history endpoint tuple from Proof 698.
theorem exists_completed_readout_of_analytic_window_selectedVisiblePrime
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (hwidth : a < c) {p : CCM24VisiblePrime}
    (hp : p ∈
      FinitePrimePowerFamily.visiblePrimes
        (FinitePrimePowerFamily.ofSelectedOwner owner))
    (hfourierAnalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ)
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
    {K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
        (sourceSoninCarrier lambda) K))
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (endpoint inclusion : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (survivor : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (data : PhysicalBoundaryDaggerReadoutContract steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      (physicalBoundaryDaggerTarget rightLeg endpoint inclusion survivor))
    (terminalReadout : sourceSoninCarrier lambda →L[ℂ] G)
    (bound : ℝ)
    (hterminal :
      terminalReadout ∘L
          juliaSurvivor (steps.map
            (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
            fixedPhysicalSourceInput owner lambda a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor =
        (rightLeg ∘L inclusion ∘L survivor) ∘L
          fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            boundaryBasis sourceBasis hfactor)
    (hjoint :
      ‖completedRectangularBoundaryReadoutOfComponents steps terminalReadout
          data.readout‖ ≤ bound)
    (hanalyticRep : ∀ y : sourceSoninCarrier lambda,
      ∃ f : ℝ → ℂ,
        AnalyticOnNhd ℝ f Set.univ ∧
          f =ᵐ[(volume : Measure ℝ)]
            (cc20GlobalLogConvolution owner.sourceTest.involution.test
              ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
                (sourceInclusion lambda y)) : ℝ → ℂ)) :
    ∃ readout : completedRectangularBoundaryCarrier steps →L[ℂ] G,
      ‖readout‖ ≤ bound ∧
        rightLeg ∘L endpoint =
          readout ∘L completedRectangularBoundaryColumn steps := by
  exact
    PhysicalBoundaryDaggerReadoutContract.exists_completed_readout_of_physicalTarget_of_denseRange
      steps
      (fixedPhysicalSourceInput owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)
      rightLeg endpoint inclusion survivor data terminalReadout bound
      hterminal hjoint
      (fixedPhysicalSourceInput_denseRange_of_analytic_window_selectedVisiblePrime
        owner lambda a c hac hsupp hwidth hp hfourierAnalytic negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
        hanalyticRep)

end CCM24FiniteSCompletedPhysicalReadoutAnalyticWindowBridge
end CCM25Concrete
end Source
end ConnesWeilRH
