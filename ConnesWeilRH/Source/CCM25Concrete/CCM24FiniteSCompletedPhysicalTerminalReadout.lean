/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEmptyPhysicalReadout

/-!
# Terminal survivor and physical boundary readout contract

The completed Schur history has two source channels:

  source input ---> terminal Julia survivor ---> fixed source right leg
              \--> raw rectangular boundary-dagger history ---> physical remainder

The first channel is unconditional. The fixed source Gram input already has
a right Douglas factor, and that factor reads the terminal survivor after the
survivor is embedded back into the finite carrier.

The second channel is not implied by Julia contraction. This module states its
exact source-specific target as a readout contract. The endpoint minus terminal
subtraction remains intact before any norm estimate. No boundary readout, Gate
3U estimate, finite-S sign, or RH conclusion is assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalTerminalReadout

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSEmptyPhysicalReadout
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedPhysicalHistory
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSFixedSourceInput
open CCM24FiniteSDouglasFactor
open CCM24FiniteSJuliaBessel
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def frameSourceInclusion (lambda : CCM24SoninScale) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.subtypeL

section FixedSourceContext

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
variable (negativeBasis : HilbertBasis iota ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis kappa ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis tau ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis iotaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis kappaR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis tauR ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
variable (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

/-! The terminal source-specific obligation is a Douglas domination. -/
set_option maxHeartbeats 4000000 in
-- The dependent survivor and fixed physical input need a larger elaboration budget.
theorem exists_fixedSource_terminal_survivor_readout_of_norm_domination
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda G p S)
    (S : List CCM24VisiblePrime)
    (hdom : ∀ x : sourceSoninCarrier lambda,
      ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        ((frameSourceInclusion lambda)
          ((juliaSurvivor
            (suffixActualSchurCoDefectSteps lambda stepData S))
            ((fixedPhysicalSourceInput owner lambda a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor) x)))‖ ≤
        ‖(juliaSurvivor
          (suffixActualSchurCoDefectSteps lambda stepData S))
          ((fixedPhysicalSourceInput owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            boundaryBasis sourceBasis hfactor) x)‖) :
    ∃ readout : sourceSoninCarrier lambda →L[ℂ] commonBoundaryCarrier a c,
      ‖readout‖ ≤ 1 ∧
        readout ∘L
            juliaSurvivor (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
            fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
              positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis
              boundaryBasis sourceBasis hfactor =
          (sourceThreeBranchPairData owner lambda a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right ∘L
            frameSourceInclusion lambda ∘L
              juliaSurvivor (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
              fixedPhysicalSourceInput owner lambda a c hac hsupp negativeBasis
                positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis
                globalBasis boundaryBasis sourceBasis hfactor := by
  let input := fixedPhysicalSourceInput owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let survivor := juliaSurvivor (suffixActualSchurCoDefectSteps lambda stepData S)
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let target := base.right ∘L frameSourceInclusion lambda ∘L survivor ∘L input
  let historyInput := survivor ∘L input
  have hdom' : ∀ x : sourceSoninCarrier lambda,
      ‖target x‖ ≤ (1 : ℝ) * ‖historyInput x‖ := by
    intro x
    simpa only [target, historyInput, input, survivor, base,
      ContinuousLinearMap.comp_apply,
      one_mul] using hdom x
  obtain ⟨readout, hnorm, hfactorization⟩ :=
    exists_factor_of_norm_le target historyInput 1 (by norm_num) hdom'
  refine ⟨readout, hnorm, ?_⟩
  simpa only [target, historyInput, input, survivor, base,
    ContinuousLinearMap.comp_apply] using hfactorization

end FixedSourceContext

/-! ## The exact raw boundary target -/

/-- The physical boundary target is the endpoint right leg with the
terminal-survivor contribution removed. The subtraction is intentionally
stored before any norm estimate. -/
noncomputable def physicalBoundaryDaggerTarget
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (rightLeg : finiteSCarrier →L[ℂ] G)
    (endpoint : H →L[ℂ] finiteSCarrier)
    (inclusion : H →L[ℂ] finiteSCarrier)
    (survivor : H →L[ℂ] H) :
    H →L[ℂ] G :=
  rightLeg ∘L endpoint - rightLeg ∘L inclusion ∘L survivor

structure PhysicalBoundaryDaggerReadoutContract
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (input : H →L[ℂ] H)
    (target : H →L[ℂ] G) where
  readout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G
  readout_norm_le_one : ‖readout‖ ≤ 1
  factorization :
    readout ∘L rectangularBoundaryDaggerColumn steps ∘L input =
      target ∘L input

/-! ## Exact component assembly -/

set_option maxHeartbeats 4000000 in
-- The completed product carrier and component bridge are elaboration-heavy.
theorem PhysicalBoundaryDaggerReadoutContract.exists_completed_readout
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (input : H →L[ℂ] H)
    (target : H →L[ℂ] G)
    (data : PhysicalBoundaryDaggerReadoutContract steps input target)
    (terminalReadout : H →L[ℂ] G)
    (terminalColumn endpointColumn : H →L[ℂ] G)
    (hterminal :
      terminalReadout ∘L
          juliaSurvivor (steps.map
            (fun step => step.toAdjointCoDefectJuliaStep)) ∘L input =
        terminalColumn)
    (hendpoint :
      terminalColumn + target ∘L input = endpointColumn)
    (hjoint :
      ‖completedRectangularBoundaryReadoutOfComponents steps terminalReadout
          data.readout‖ ≤ 1) :
    ∃ readout : completedRectangularBoundaryCarrier steps →L[ℂ] G,
      ‖readout‖ ≤ 1 ∧
        endpointColumn =
          readout ∘L completedRectangularBoundaryColumn steps ∘L input := by
  let readout :=
    completedRectangularBoundaryReadoutOfComponents steps terminalReadout
      data.readout
  refine ⟨readout, hjoint, ?_⟩
  have hcomponent :=
    completedRectangularBoundaryReadoutOfComponents_comp_column_eq_add
      steps input terminalReadout data.readout terminalColumn
      (target ∘L input) hterminal data.factorization
  apply ContinuousLinearMap.ext
  intro x
  have hsum := congrArg
    (fun operator : H →L[ℂ] G => operator x) hendpoint
  have hcolumn := congrArg
    (fun operator : H →L[ℂ] G => operator x) hcomponent
  calc
    endpointColumn x = terminalColumn x + (target ∘L input) x := by
      simpa only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply] using hsum.symm
    _ = readout
        (completedRectangularBoundaryColumn steps (input x)) := by
      simpa only [readout, ContinuousLinearMap.comp_apply] using hcolumn.symm

end CCM24FiniteSCompletedPhysicalTerminalReadout
end CCM25Concrete
end Source
end ConnesWeilRH
