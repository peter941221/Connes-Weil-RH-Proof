/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar

/-!
# Current-range consumers on the actual fixed-quotient band carrier

The fixed-quotient first jet acts on `Ran(E - R)`.  This module specializes
the carrier-correct producer to the finite Euler inverse and reconnects its
nonzero response to the existing factorized current-range Julia and Douglas
consumers.

The older source-Sonin versions remain useful only as semantic guards: their
right band input is zero.  The post-root adapters below are abstract because
their Julia steps live on the packed boundary root.  The final rectangular
adapter instead uses the actual source-Sonin Euler schedule and keeps its
physical input distinct from the compact boundary carrier.

No Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedQuotientBandConsumer

open MeasureTheory
open CC20Concrete
open scoped InnerProduct InnerProductSpace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalSupport
open CCM24FiniteSBandTrace
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedSourcePolar
open CCM24SourceProlateTrace

noncomputable local instance sourceBandCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceBandCarrier lambda) :=
  (sourceBandClosedRange lambda).isClosed.completeSpace_coe

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

-- Cache the topology before the Julia column adds a dependent `PiLp` layer.
noncomputable local instance sourceBandFixedQuotientBoundaryTopology
    (a c : ℝ) : TopologicalSpace
      (fixedQuotientFirstJetBoundaryCarrier a c) :=
  inferInstance

set_option maxHeartbeats 1000000 in
-- The four-coordinate producer is expensive to unfold through both branches.
/-- The corrected producer read back through the two physical second-support
branches, on `Ran(E - R)` rather than on the annihilated Sonin carrier. -/
theorem sourceBandFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceBandFixedQuotientFirstJetInputSideProducer owner lambda a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      bandBasis hfactor transport).response =
      (sourceBandInclusion lambda)† ∘L
        (sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L transport ∘L
          sourceBandProjection lambda) ∘L sourceBandInclusion lambda +
        (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L transport ∘L
          sourceBandProjection lambda ∘L sourceBandInclusion lambda := by
  rw [sourceBandFixedQuotientFirstJetInputSideProducer_response_eq_corner owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis bandBasis hfactor transport]
  have hcompression :
      sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  rw [hcompression]
  exact sourceBandFixedQuotientCorner_eq_secondSupport_twoBranch
    owner lambda transport

set_option maxHeartbeats 1000000 in
-- The result type contains the complete four-coordinate boundary carrier.
/-- Finite Euler specialization of the carrier-correct fixed-quotient first
jet producer. -/
noncomputable def sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis :=
  sourceBandFixedQuotientFirstJetInputSideProducer owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    bandBasis hfactor
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

set_option maxHeartbeats 1000000 in
-- Elaborating the readback exposes the complete carrier-correct producer.
theorem sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis bandBasis hfactor).response =
      (sourceBandInclusion lambda)† ∘L
        (sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda) ∘L sourceBandInclusion lambda +
        (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda ∘L sourceBandInclusion lambda := by
  exact sourceBandFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis bandBasis hfactor
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

set_option maxHeartbeats 1000000 in
-- The Julia column adds a dependent product above the boundary carrier.
/-- Current-range Douglas estimate for the nonzero band-carrier response. -/
theorem sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis)
    (hbase : base =
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factor : PiLp 2
      (fun _ : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length =>
        fixedQuotientFirstJetBoundaryCarrier a c) →L[ℂ]
      fixedQuotientFirstJetBoundaryCarrier a c)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn
          (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (bandBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root (base.rightInput (bandBasis i))‖ ^ 2)) := by
  have hresponse : base.response =
      (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor).response := by
    rw [hbase]
  exact inputSideFactorizedCurrentRangeDouglas_ordinaryTrace_norm_le_of_response
    base _ hresponse causalSteps factor factorBound factorBound_nonneg
    factor_norm_le factorization

set_option maxHeartbeats 1000000 in
-- The readout theorem elaborates the same dependent Julia column.
/-- Finite-coordinate readout form of the band-carrier Douglas estimate. -/
theorem sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis)
    (hbase : base =
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (readout : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length →
      fixedQuotientFirstJetBoundaryCarrier a c →L[ℂ]
        fixedQuotientFirstJetBoundaryCarrier a c)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        inputSidePiLpReadoutSum readout ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (bandBasis i))‖ ^ 2) +
          (∑ i, ‖readout i‖) ^ 2 *
            (∑' i, ‖base.root (base.rightInput (bandBasis i))‖ ^ 2)) := by
  exact sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis bandBasis hfactor base hbase causalSteps
    (inputSidePiLpReadoutSum readout) (∑ i, ‖readout i‖)
    (Finset.sum_nonneg fun i _ => norm_nonneg (readout i))
    (norm_inputSidePiLpReadoutSum_le readout) physicalColumn_eq_readout

set_option maxHeartbeats 1000000 in
-- Douglas generation unfolds the full carrier-correct right column.
/-- Pointwise operator-domination form on every vector of `Ran(E - R)`. -/
theorem sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis)
    (hbase : base =
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : sourceBandCarrier lambda,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ≤
        factorBound *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (bandBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root (base.rightInput (bandBasis i))‖ ^ 2)) := by
  let producer :=
    douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorDomination
      base causalSteps factorBound factorBound_nonneg hdom
  have hfactorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        producer.factor ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput) := by
    exact producer.factorization
  exact sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis bandBasis hfactor base hbase causalSteps
    producer.factor producer.factorBound producer.factorBound_nonneg
    producer.factor_norm_le hfactorization

set_option maxHeartbeats 1000000 in
-- The positive-operator form unfolds the full carrier-correct right column.
/-- Squared-norm operator-domination form on the actual band carrier. -/
theorem sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeNormSqDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis)
    (hbase : base =
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : sourceBandCarrier lambda,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ^ 2 ≤
        factorBound ^ 2 *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (bandBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root (base.rightInput (bandBasis i))‖ ^ 2)) := by
  let producer :=
    douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorNormSqDomination
      base causalSteps factorBound factorBound_nonneg hdom
  have hfactorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        producer.factor ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput) := by
    exact producer.factorization
  exact sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis bandBasis hfactor base hbase causalSteps
    producer.factor producer.factorBound producer.factorBound_nonneg
    producer.factor_norm_le hfactorization

/-!
The actual fixed-source Julia schedule acts on `sourceSoninCarrier`, whereas
the canonical Hilbert--Schmidt packing has a boundary root carrier.  The next
consumer keeps those carriers separate.  It controls the physical right leg
through a Julia range column applied to an explicit rectangular source input.
-/

theorem inputSideRectangularJuliaReadout_ordinaryTrace_norm_le
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (steps : List (JuliaDefectStep D G))
    (physicalInput : H →L[ℂ] D)
    (readout : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G)
    (readoutBound : ℝ)
    (readout_norm_le : ‖readout‖ ≤ readoutBound)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        readout ∘L (juliaRangeColumn steps ∘L physicalInput))
    (rangeColumn_summable : Summable fun i =>
      ‖juliaRangeColumn steps (physicalInput (sourceBasis i))‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (sourceBasis i))‖ ^ 2) +
          readoutBound ^ 2 *
            (∑' i,
              ‖juliaRangeColumn steps (physicalInput (sourceBasis i))‖ ^ 2)) := by
  let rightMajorant : ι → ℝ := fun i =>
    readoutBound ^ 2 *
      ‖juliaRangeColumn steps (physicalInput (sourceBasis i))‖ ^ 2
  have hright_nonneg : ∀ i, 0 ≤ rightMajorant i := by
    intro i
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hright_summable : Summable rightMajorant := by
    simpa only [rightMajorant] using
      rangeColumn_summable.mul_left (readoutBound ^ 2)
  have hright_point : ∀ i,
      ‖base.rightFactor (base.root (base.rightInput (sourceBasis i)))‖ ^ 2 ≤
        rightMajorant i := by
    intro i
    have hfactorization := congrArg
      (fun T : H →L[ℂ] G => T (sourceBasis i)) physicalColumn_eq_readout
    simp only [ContinuousLinearMap.comp_apply] at hfactorization
    rw [hfactorization]
    calc
      ‖readout (juliaRangeColumn steps
          (physicalInput (sourceBasis i)))‖ ^ 2 ≤
          (‖readout‖ * ‖juliaRangeColumn steps
            (physicalInput (sourceBasis i))‖) ^ 2 := by
        gcongr
        exact readout.le_opNorm _
      _ ≤ (readoutBound * ‖juliaRangeColumn steps
          (physicalInput (sourceBasis i))‖) ^ 2 := by
        gcongr
      _ = rightMajorant i := by
        simp only [rightMajorant]
        ring
  have hbound :=
    inputSideRootS2Producer_ordinaryTrace_norm_le_of_right_majorant
      base rightMajorant hright_nonneg hright_summable hright_point
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        base.response‖ ≤
        (1 / 2 : ℝ) *
          (‖base.leftFactor‖ ^ 2 *
              (∑' i, ‖base.root (base.leftInput (sourceBasis i))‖ ^ 2) +
            ∑' i, rightMajorant i) := hbound
    _ = (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (sourceBasis i))‖ ^ 2) +
          readoutBound ^ 2 *
            (∑' i,
              ‖juliaRangeColumn steps (physicalInput (sourceBasis i))‖ ^ 2)) := by
      simp only [rightMajorant]
      rw [tsum_mul_left]

/-!
The packed common-root producer does not expose the original right leg
directly: it places that leg in the first coordinate of a second `L2` pair.
Name this isometric coordinate injection before reading back the physical
fixed-quotient column.
-/
noncomputable def commonRootRightEmbedding
    {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    G →L[ℂ] WithLp 2 (G × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ G G).symm.toContinuousLinearMap ∘L
    ((ContinuousLinearMap.id ℂ G).prod (0 : G →L[ℂ] G))

@[simp]
theorem commonRootRightEmbedding_apply
    {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (x : G) :
    commonRootRightEmbedding x = WithLp.toLp 2 (x, 0) := by
  simp [commonRootRightEmbedding]

/-- The input-side common-root right column is exactly the original
Hilbert--Schmidt right leg followed by the named coordinate embedding. -/
theorem inputSideRootS2ProducerOfPairData_rightColumn_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    (inputSideRootS2ProducerOfPairData data).rightFactor ∘L
          (inputSideRootS2ProducerOfPairData data).root ∘L
          (inputSideRootS2ProducerOfPairData data).rightInput =
      commonRootRightEmbedding ∘L data.right := by
  apply ContinuousLinearMap.ext
  intro x
  simp [inputSideRootS2ProducerOfPairData, commonRootS2ProducerOfPairData,
    commonRootSecondCoordinate_apply]

/-- The literal band-to-Sonin input in the finite Euler first jet:
`J_R† E A_S E J_B`. -/
noncomputable def sourceBandFiniteEulerSoninInput
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda ∘L
    sourceBandInclusion lambda

/-- Reading the rectangular input back into the ambient carrier gives the
actual Sonin-compressed finite Euler band input. -/
theorem sourceInclusion_comp_sourceBandFiniteEulerSoninInput
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceInclusion lambda ∘L sourceBandFiniteEulerSoninInput lambda family =
      sourceSoninProjection lambda ∘L radialSupportProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda ∘L
        sourceBandInclusion lambda := by
  rw [sourceBandFiniteEulerSoninInput, ← ContinuousLinearMap.comp_assoc,
    sourceInclusion_comp_adjoint]

/-- The fixed physical pair's right leg, restricted to the genuine source
Sonin carrier and embedded in the packed common-root output coordinate. -/
noncomputable def sourceFixedQuotientPhysicalRightColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceSoninCarrier lambda →L[ℂ]
      fixedQuotientFirstJetBoundaryCarrier a c :=
  commonRootRightEmbedding ∘L
    (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor).right ∘L
    sourceInclusion lambda

set_option maxHeartbeats 2000000 in
-- The readback unfolds the four-coordinate pair through both bounded
-- constructor layers, but uses only the three exact projection identities.
/-- The complete finite-Euler band right column factors through the literal
rectangular band-to-Sonin input and one fixed physical source column. -/
theorem sourceBandFiniteEulerFixedQuotientFirstJet_rightColumn_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    let base :=
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor
    base.rightFactor ∘L base.root ∘L base.rightInput =
      sourceFixedQuotientPhysicalRightColumn owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis
          boundaryBasis hfactor ∘L
        sourceBandFiniteEulerSoninInput lambda family := by
  dsimp only
  unfold sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer
  unfold sourceBandFixedQuotientFirstJetInputSideProducer
  rw [inputSideRootS2ProducerOfPairData_rightColumn_eq]
  simp only [
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp,
    sourceFixedQuotientFirstJetPairData, fixedQuotientFirstJetPairData,
    boundedFirstJetPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    sourceFixedQuotientPhysicalRightColumn]
  have hband := congrArg
    (fun T : sourceBandCarrier lambda →L[ℂ] finiteSCarrier => T x)
    (sourceBandProjection_comp_sourceBandInclusion lambda)
  have hinput := congrArg
    (fun T : sourceBandCarrier lambda →L[ℂ] finiteSCarrier => T x)
    (sourceInclusion_comp_sourceBandFiniteEulerSoninInput lambda family)
  have hcompression :
      sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) =
        sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  simp only [ContinuousLinearMap.comp_apply] at hband hinput
  rw [hband, hcompression, hinput]

/-!
This is the route-facing current-range consumer.  Unlike the post-root
adapters above, its step list is generated by the actual suffix-dependent
finite Euler Schur data on `sourceSoninCarrier`.  The two remaining premises
are therefore honest: the completed physical right column must equal the
named readout, and that named source Julia column must be Hilbert--Schmidt
along the band basis.
-/
set_option maxHeartbeats 2000000 in
-- The theorem elaborates both the four-coordinate boundary pair and the
-- suffix-dependent source-Sonin Julia schedule.  Local aliases below keep
-- those two large dependent expressions shared during the final readback.
theorem sourceBandEulerFixedQuotient_ordinaryTrace_norm_le_of_actualCurrentRangeReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) bandBasis)
    (hbase : base =
      sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor)
    (S : List CCM24VisiblePrime)
    (stepData : ∀ (p : CCM24VisiblePrime) (suffix : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda
        (fixedQuotientFirstJetBoundaryCarrier a c) p suffix)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        inputSidePiLpReadoutSum
            (fixedSourceCurrentRangeJuliaReadout lambda stepData S) ∘L
          (juliaRangeColumn
              (currentRangeJuliaSteps
                (fixedSourceCurrentRangeJuliaSteps lambda stepData S)) ∘L
            sourceBandFiniteEulerSoninInput lambda family))
    (rangeColumn_summable : Summable fun i =>
      ‖juliaRangeColumn
          (currentRangeJuliaSteps
            (fixedSourceCurrentRangeJuliaSteps lambda stepData S))
          (sourceBandFiniteEulerSoninInput lambda family (bandBasis i))‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (bandBasis i))‖ ^ 2) +
          (∑ i, ‖fixedSourceCurrentRangeJuliaReadout lambda stepData S i‖) ^ 2 *
            (∑' i,
              ‖juliaRangeColumn
                  (currentRangeJuliaSteps
                    (fixedSourceCurrentRangeJuliaSteps lambda stepData S))
                  (sourceBandFiniteEulerSoninInput lambda family
                    (bandBasis i))‖ ^ 2)) := by
  have hresponse : base.response =
      (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor).response := by
    rw [hbase]
  rw [← hresponse]
  let actualSteps : List (JuliaDefectStep (sourceSoninCarrier lambda)
      (fixedQuotientFirstJetBoundaryCarrier a c)) :=
    currentRangeJuliaSteps
      (fixedSourceCurrentRangeJuliaSteps lambda stepData S)
  let actualInput : sourceBandCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    sourceBandFiniteEulerSoninInput lambda family
  let actualReadout :
      PiLp 2 (fun _ : Fin actualSteps.length =>
        fixedQuotientFirstJetBoundaryCarrier a c) →L[ℂ]
          fixedQuotientFirstJetBoundaryCarrier a c :=
    inputSidePiLpReadoutSum
      (fixedSourceCurrentRangeJuliaReadout lambda stepData S)
  let actualReadoutBound : ℝ :=
    ∑ i, ‖fixedSourceCurrentRangeJuliaReadout lambda stepData S i‖
  have hreadout : ‖actualReadout‖ ≤ actualReadoutBound := by
    simpa only [actualSteps, actualReadout, actualReadoutBound] using
      (norm_inputSidePiLpReadoutSum_le
        (fixedSourceCurrentRangeJuliaReadout lambda stepData S))
  have hphysical :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        actualReadout ∘L (juliaRangeColumn actualSteps ∘L actualInput) := by
    simpa only [actualSteps, actualInput, actualReadout] using
      physicalColumn_eq_readout
  have hrange : Summable fun i =>
      ‖juliaRangeColumn actualSteps (actualInput (bandBasis i))‖ ^ 2 := by
    simpa only [actualSteps, actualInput] using rangeColumn_summable
  exact inputSideRectangularJuliaReadout_ordinaryTrace_norm_le
    (H := sourceBandCarrier lambda)
    (K := fixedQuotientFirstJetBoundaryCarrier a c)
    (D := sourceSoninCarrier lambda)
    (G := fixedQuotientFirstJetBoundaryCarrier a c)
    (sourceBasis := bandBasis) base actualSteps actualInput actualReadout
    actualReadoutBound hreadout hphysical hrange

end CCM24FiniteSFixedQuotientBandConsumer
end CCM25Concrete
end Source
end ConnesWeilRH
