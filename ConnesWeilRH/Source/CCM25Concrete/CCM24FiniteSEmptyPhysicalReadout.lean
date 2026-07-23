/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistory
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourceInput
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInput
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPolarTraceBridge

/-!
# Empty visible-prime physical readout

The completed history has a nonzero survivor coordinate even when the visible
prime list is empty.  This module records the exact base case on the actual
source carrier.  The fixed physical source input is the positive Gram square
root of the two-branch pair, and its bounded right Douglas factor is the
terminal readout.  No nonempty-family physical identity is inferred here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEmptyPhysicalReadout

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactConvolutionSupport
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCausalSupport
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCoframeResponse
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSFixedSourceInput
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSJuliaBessel
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSSchurMarkovPolarTraceBridge

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The empty family and its visible list -/

noncomputable def emptyFinitePrimePowerFamily : FinitePrimePowerFamily where
  terms := ∅
  prime := by simp
  exponent_ne_zero := by simp

@[simp]
theorem emptyFinitePrimePowerFamily_visiblePrimes :
    emptyFinitePrimePowerFamily.visiblePrimes = [] := by
  rw [FinitePrimePowerFamily.visiblePrimes]
  simp [emptyFinitePrimePowerFamily]

/-! ## Empty endpoint coframes -/

theorem normalizedFiniteEulerInverse_eq_id_of_visiblePrimes_nil
    (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    normalizedFiniteEulerInverse family =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  unfold normalizedFiniteEulerInverse finiteEulerInverseOperator
  rw [hvisible, ccm24FiniteEulerTransportEquiv_nil]
  simp [finiteEulerLowerFactor]

theorem sourceActualBandForwardCoframe_eq_zero_of_visiblePrimes_nil
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    sourceActualBandForwardCoframe lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hband := DFunLike.congr_fun
    (sourceBandProjection_comp_sourceInclusion_eq_zero lambda) x
  simp only [sourceActualBandForwardCoframe,
    ContinuousLinearMap.comp_apply,
    normalizedFiniteEulerInverse_eq_id_of_visiblePrimes_nil family hvisible,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hband ⊢
  exact hband

theorem finiteEulerMetricCoframe_eq_sourceInclusion_of_visiblePrimes_nil
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    finiteEulerMetricCoframe lambda family = sourceInclusion lambda := by
  rw [finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame]
  rw [finiteEulerTransportOperator, hvisible,
    ccm24FiniteEulerTransportEquiv_nil]
  rw [finiteEulerDualFrame, finiteEulerFrame_eq_transport_comp_inclusion,
    hvisible, ccm24FiniteEulerTransportEquiv_nil,
    ← parameterizedSoninGramInv_one_eq_finiteEulerGramInv,
    hvisible,
    parameterizedSoninGramInv_one_nil_eq_id]
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem sourceActualBandForwardEndpointCoframe_eq_sourceInclusion_of_visiblePrimes_nil
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    sourceActualBandForwardEndpointCoframe lambda family =
      sourceInclusion lambda := by
  rw [sourceActualBandForwardEndpointCoframe,
    sourceActualBandForwardCoframe_eq_zero_of_visiblePrimes_nil
      lambda family hvisible,
    finiteEulerMetricCoframe_eq_sourceInclusion_of_visiblePrimes_nil
      lambda family hvisible]
  simp

/-! ## The exact terminal component factorization -/

theorem fixedSourceRight_eq_sourceThreeBranchRight_comp_inclusion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis
      boundaryBasis sourceBasis hfactor).right =
      (sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right ∘L
        sourceInclusion lambda := by
  rfl

/-! ## The terminal Douglas readout -/

noncomputable def fixedSourceRightReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceSoninCarrier lambda →L[ℂ] commonBoundaryCarrier a c :=
  (SourceGramInputFactorData.ofPairData
    (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)).rightFactor

theorem fixedSourceRightReadout_norm_le_one
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖fixedSourceRightReadout owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor‖ ≤ 1 := by
  exact
    (SourceGramInputFactorData.ofPairData
      (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)).rightFactor_norm_le_one

theorem fixedSourceRightReadout_comp_input_eq_pair_right
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    fixedSourceRightReadout owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor ∘L
      fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor =
      (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).right := by
  exact
    (SourceGramInputFactorData.ofPairData
      (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor)).rightFactorization

/-! ## The completed empty-family readout -/

set_option maxHeartbeats 4000000 in
-- The dependent completed-history carrier needs a larger elaboration budget.
theorem exists_empty_completed_physical_readout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
        lambda (commonBoundaryCarrier a c) p S) :
    ∃ readout : completedRectangularBoundaryCarrier
        (suffixActualSchurFrameSteps lambda stepData
          emptyFinitePrimePowerFamily.visiblePrimes) →L[ℂ]
        commonBoundaryCarrier a c,
      ‖readout‖ ≤ 1 ∧
        (sourceThreeBranchPairData owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda
            emptyFinitePrimePowerFamily =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData
            emptyFinitePrimePowerFamily.visiblePrimes) ∘L
          fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis hfactor := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let input := fixedPhysicalSourceInput owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let terminal := fixedSourceRightReadout owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let steps := suffixActualSchurFrameSteps lambda stepData
    emptyFinitePrimePowerFamily.visiblePrimes
  let boundary : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => finiteSCarrier) →L[ℂ]
      commonBoundaryCarrier a c := 0
  let readout := completedRectangularBoundaryReadoutOfComponents steps
    terminal boundary
  have hsteps : steps = [] := by
    dsimp only [steps]
    simp [emptyFinitePrimePowerFamily_visiblePrimes,
      suffixActualSchurFrameSteps]
  have hterminal : terminal ∘L
      juliaSurvivor (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)) ∘L input =
      base.right ∘L sourceInclusion lambda := by
    rw [hsteps]
    simp only [List.map_nil, juliaSurvivor,
      ContinuousLinearMap.id_comp]
    dsimp only [terminal, input, base]
    rw [fixedSourceRightReadout_comp_input_eq_pair_right]
    exact fixedSourceRight_eq_sourceThreeBranchRight_comp_inclusion
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hboundary : boundary ∘L rectangularBoundaryDaggerColumn steps ∘L input =
      0 := by
    apply ContinuousLinearMap.ext
    intro x
    simp [boundary]
  have hcomponent :=
    completedRectangularBoundaryReadoutOfComponents_comp_column_eq_add
      steps input terminal boundary (base.right ∘L sourceInclusion lambda) 0
      hterminal hboundary
  have hnorm : ‖readout‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [show readout x = terminal x.fst + boundary x.snd by
      exact completedRectangularBoundaryReadoutOfComponents_apply
        steps terminal boundary x]
    rw [show boundary x.snd = 0 by rfl, add_zero]
    calc
      ‖terminal x.fst‖ ≤ ‖terminal‖ * ‖x.fst‖ := terminal.le_opNorm _
      _ ≤ 1 * ‖x.fst‖ := by
        exact mul_le_mul_of_nonneg_right
          (fixedSourceRightReadout_norm_le_one owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis hfactor) (norm_nonneg _)
      _ = ‖x.fst‖ := one_mul _
      _ ≤ 1 * ‖x‖ := by
        rw [one_mul]
        exact WithLp.norm_fst_le (α := _) (β := _) (p := 2) x
  refine ⟨readout, hnorm, ?_⟩
  rw [sourceActualBandForwardEndpointCoframe_eq_sourceInclusion_of_visiblePrimes_nil
    lambda emptyFinitePrimePowerFamily emptyFinitePrimePowerFamily_visiblePrimes]
  simpa [readout, steps, input, base] using hcomponent.symm

end CCM24FiniteSEmptyPhysicalReadout
end CCM25Concrete
end Source
end ConnesWeilRH
