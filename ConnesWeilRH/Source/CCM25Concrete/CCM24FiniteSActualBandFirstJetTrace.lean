/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandJetOrientation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientContractionBound

/-!
# Actual finite-S band first-jet trace owner

Proof 438 identifies the direction missed by the Proof 436 paired jet.  This
module constructs the correctly oriented detector response from two bounded
sandwiches of the already completed physical boundary pair.  Trace legality
therefore comes from genuine Hilbert--Schmidt legs and not from cycling an
unbounded whole-line product.

No endpoint-remainder estimate, Gate 3U premise, finite-S sign, Burnol
identity, or RH premise is used here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualBandFirstJetTrace

open CC20Concrete
open MeasureTheory
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInverseMetric
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CCM24FiniteSActualBandJetOrientation
open CC20Concrete.CompactRootHalfLinePair

/-! ## Generic actual-orientation algebra -/

variable {A : Type*} [Ring A]

/-- The common-support detector response in the actual band orientation. -/
def actualBandDetectorPairedResponse
    (band inner detector transport transportAdjoint : A) : A :=
  inner * detector * band * transport * inner +
    inner * transportAdjoint * band * detector * inner

/-- The same response written with the fixed detector commutator. -/
def actualBandCommutatorPairedResponse
    (band inner detector transport transportAdjoint : A) : A :=
  -(inner *
      CCM24FiniteSTwoSidedRootRecombination.commutator detector inner *
      band * transport * inner) +
    inner * transportAdjoint * band *
      CCM24FiniteSTwoSidedRootRecombination.commutator detector inner * inner

theorem actualBandCommutatorPairedResponse_eq_detector
    (band inner detector transport transportAdjoint : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0) :
    actualBandCommutatorPairedResponse band inner detector transport
        transportAdjoint =
      actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint := by
  have hInnerSq : inner * inner = inner := hInner
  have hForward :
      -(inner *
          CCM24FiniteSTwoSidedRootRecombination.commutator detector inner *
          band * transport * inner) =
        inner * detector * band * transport * inner := by
    unfold CCM24FiniteSTwoSidedRootRecombination.commutator
    calc
      -(inner * (detector * inner - inner * detector) * band * transport *
          inner) =
          -(inner * detector * (inner * band) * transport * inner -
            (inner * inner) * detector * band * transport * inner) := by
              noncomm_ring
      _ = inner * detector * band * transport * inner := by
        rw [hInnerBand, hInnerSq]
        noncomm_ring
  have hReverse :
      inner * transportAdjoint * band *
          CCM24FiniteSTwoSidedRootRecombination.commutator detector inner *
          inner =
        inner * transportAdjoint * band * detector * inner := by
    unfold CCM24FiniteSTwoSidedRootRecombination.commutator
    calc
      inner * transportAdjoint * band *
          (detector * inner - inner * detector) * inner =
        inner * transportAdjoint * band * detector * (inner * inner) -
          inner * transportAdjoint * (band * inner) * detector * inner := by
            noncomm_ring
      _ = inner * transportAdjoint * band * detector * inner := by
        rw [hInnerSq, hBandInner]
        noncomm_ring
  unfold actualBandCommutatorPairedResponse
    actualBandDetectorPairedResponse
  rw [hForward, hReverse]

/-! ## Generic Hilbert--Schmidt pair producer -/

/-- Two bounded sandwiches of one fixed-commutator pair.  Their signs and
orientations are assembled before the ordinary trace is taken. -/
noncomputable def actualBandCommutatorPairData
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport transportAdjoint : H →L[ℂ] H) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × G)) sourceBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    ((sourceData.boundedSandwich targetBasis inner
      (band ∘L transport ∘L inner)).smulRight (-1))
    (sourceData.boundedSandwich targetBasis
      (inner ∘L transportAdjoint ∘L band) inner)

theorem actualBandCommutatorPairData_traceProduct_eq
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner detector transport transportAdjoint : H →L[ℂ] H)
    (hSource : sourceData.traceProduct =
      CCM24FiniteSTwoSidedRootRecombination.commutator detector inner)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0) :
    (actualBandCommutatorPairData targetBasis sourceData band inner transport
      transportAdjoint).traceProduct =
      actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint := by
  rw [actualBandCommutatorPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    hSource]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, neg_smul, one_smul]
  simpa only [ContinuousLinearMap.mul_def] using congrFun
    (congrArg DFunLike.coe
      (actualBandCommutatorPairedResponse_eq_detector band inner detector
        transport transportAdjoint hInner hBandInner hInnerBand)) u

theorem actualBandCommutatorPairData_isTraceClassAlong
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner detector transport transportAdjoint : H →L[ℂ] H)
    (hSource : sourceData.traceProduct =
      CCM24FiniteSTwoSidedRootRecombination.commutator detector inner)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint) := by
  rw [← actualBandCommutatorPairData_traceProduct_eq targetBasis sourceData
    band inner detector transport transportAdjoint hSource hInner hBandInner
    hInnerBand]
  exact (actualBandCommutatorPairData targetBasis sourceData band inner
    transport transportAdjoint).traceProduct_isTraceClassAlong

/-- If all four exposed corner maps are contractions, the actual-orientation
trace is bounded by the square energy of the one fixed commutator pair. -/
theorem actualBandCommutatorPairData_ordinaryTrace_norm_le_sourceEnergy
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport transportAdjoint : H →L[ℂ] H)
    (hInner : ‖inner‖ ≤ 1)
    (hForward : ‖band ∘L transport ∘L inner‖ ≤ 1)
    (hReverse : ‖inner ∘L transportAdjoint ∘L band‖ ≤ 1) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (actualBandCommutatorPairData targetBasis sourceData band inner
          transport transportAdjoint).traceProduct‖ ≤
      (∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2 := by
  let forwardBase := sourceData.boundedSandwich targetBasis inner
    (band ∘L transport ∘L inner)
  let forward := forwardBase.smulRight (-1)
  let reverse := sourceData.boundedSandwich targetBasis
    (inner ∘L transportAdjoint ∘L band) inner
  let pair := CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    forward reverse
  have hPair :
      actualBandCommutatorPairData targetBasis sourceData band inner transport
        transportAdjoint = pair := by
    rfl
  rw [hPair]
  have hForwardLeftBase := boundedSandwich_left_tsum_le_of_norm_le_one
    targetBasis sourceData inner (band ∘L transport ∘L inner) hInner
  have hForwardRightBase := boundedSandwich_right_tsum_le_of_norm_le_one
    targetBasis sourceData inner (band ∘L transport ∘L inner) hForward
  have hReverseLeft := boundedSandwich_left_tsum_le_of_norm_le_one
    targetBasis sourceData (inner ∘L transportAdjoint ∘L band) inner hReverse
  have hReverseRight := boundedSandwich_right_tsum_le_of_norm_le_one
    targetBasis sourceData (inner ∘L transportAdjoint ∘L band) inner hInner
  have hForwardLeft :
      (∑' i, ‖forward.left (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2 := by
    simpa only [forward,
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight] using
        hForwardLeftBase
  have hForwardRight :
      (∑' i, ‖forward.right (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2 := by
    have hEnergy :
        (∑' i, ‖forward.right (sourceBasis i)‖ ^ 2) =
          ∑' i, ‖forwardBase.right (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      simp only [forward,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
        neg_smul, one_smul,
        ContinuousLinearMap.neg_apply, norm_neg]
    rw [hEnergy]
    exact hForwardRightBase
  have hPairLeft :
      (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) ≤
        2 * (∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2) := by
    dsimp only [pair]
    rw [l2Sum_left_basisEnergy_eq_add]
    dsimp only [reverse]
    linarith
  have hPairRight :
      (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) ≤
        2 * (∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2) := by
    dsimp only [pair]
    rw [l2Sum_right_basisEnergy_eq_add]
    dsimp only [reverse]
    linarith
  have hTrace := inputSideRootS2ProducerOfPairData_ordinaryTrace_norm_le pair
  rw [inputSideRootS2ProducerOfPairData_response_eq] at hTrace
  calc
    _ ≤ (1 / 2 : ℝ) *
        ((∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) := hTrace
    _ ≤ (∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2 := by
      nlinarith

/-! ## Actual CCM24 source producer -/

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The actual paired first-jet response with the selected detector compressed
to the common radial support. -/
noncomputable def sourceActualBandFiniteEulerPairedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  actualBandDetectorPairedResponse (sourceBandProjection lambda)
    (sourceSoninProjection lambda)
    (compressedDetector (radialSupportProjection lambda)
      (detectorOperator owner))
    (normalizedFiniteEulerInverse family)
    (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))

theorem fixedPhysicalCommutator_eq_sourceCompressedCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) =
      CCM24FiniteSTwoSidedRootRecombination.commutator
        (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner))
        (sourceSoninProjection lambda) := by
  have hSource :
      sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) =
        sourceSoninProjection lambda := by
    simpa only [sourceCompression, ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  rw [← compressed_source_commutator_eq_physical
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda) (detectorOperator owner)
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
    (by simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceProlateRemainder lambda)
    (by simpa only [ContinuousLinearMap.mul_def] using
      sourceProlateRemainder_comp_radialSupportProjection lambda), hSource]

/-- The same response may use the uncompressed detector because every exposed
corner is already supported by `E`. -/
theorem sourceActualBandFiniteEulerPairedResponse_eq_rawDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerPairedResponse owner lambda family =
      actualBandDetectorPairedResponse (sourceBandProjection lambda)
        (sourceSoninProjection lambda) (detectorOperator owner)
        (normalizedFiniteEulerInverse family)
        (ContinuousLinearMap.adjoint
          (normalizedFiniteEulerInverse family)) := by
  have hInnerSupport : sourceSoninProjection lambda *
      radialSupportProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_radialSupportProjection lambda
  have hSupportInner : radialSupportProjection lambda *
      sourceSoninProjection lambda = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceSoninProjection lambda
  have hBandSupport : sourceBandProjection lambda *
      radialSupportProjection lambda = sourceBandProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_radialSupportProjection_eq_self lambda
  have hSupportBand : radialSupportProjection lambda *
      sourceBandProjection lambda = sourceBandProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_sourceBandProjection_eq_self lambda
  have hForwardDetector :
      sourceSoninProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceBandProjection lambda =
        sourceSoninProjection lambda * detectorOperator owner *
          sourceBandProjection lambda := by
    calc
      _ = (sourceSoninProjection lambda * radialSupportProjection lambda) *
          detectorOperator owner *
            (radialSupportProjection lambda * sourceBandProjection lambda) := by
              noncomm_ring
      _ = _ := by rw [hInnerSupport, hSupportBand]
  have hReverseDetector :
      sourceBandProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceSoninProjection lambda =
        sourceBandProjection lambda * detectorOperator owner *
          sourceSoninProjection lambda := by
    calc
      _ = (sourceBandProjection lambda * radialSupportProjection lambda) *
          detectorOperator owner *
            (radialSupportProjection lambda * sourceSoninProjection lambda) := by
              noncomm_ring
      _ = _ := by rw [hBandSupport, hSupportInner]
  unfold sourceActualBandFiniteEulerPairedResponse
    actualBandDetectorPairedResponse compressedDetector
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceSoninProjection lambda *
            (radialSupportProjection lambda * detectorOperator owner *
              radialSupportProjection lambda) *
            sourceBandProjection lambda *
          normalizedFiniteEulerInverse family * sourceSoninProjection lambda +
        sourceSoninProjection lambda *
            ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family) *
            sourceBandProjection lambda *
          (radialSupportProjection lambda * detectorOperator owner *
            radialSupportProjection lambda) *
          sourceSoninProjection lambda =
      sourceSoninProjection lambda * detectorOperator owner *
            sourceBandProjection lambda * normalizedFiniteEulerInverse family *
          sourceSoninProjection lambda +
        sourceSoninProjection lambda *
            ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family) *
          sourceBandProjection lambda * detectorOperator owner *
          sourceSoninProjection lambda by
    calc
      _ = (sourceSoninProjection lambda *
              (radialSupportProjection lambda * detectorOperator owner *
                radialSupportProjection lambda) *
              sourceBandProjection lambda) *
            normalizedFiniteEulerInverse family *
            sourceSoninProjection lambda +
          sourceSoninProjection lambda *
            ContinuousLinearMap.adjoint
              (normalizedFiniteEulerInverse family) *
            (sourceBandProjection lambda *
              (radialSupportProjection lambda * detectorOperator owner *
                radialSupportProjection lambda) *
              sourceSoninProjection lambda) := by
                noncomm_ring
      _ = (sourceSoninProjection lambda * detectorOperator owner *
              sourceBandProjection lambda) *
            normalizedFiniteEulerInverse family *
            sourceSoninProjection lambda +
          sourceSoninProjection lambda *
            ContinuousLinearMap.adjoint
              (normalizedFiniteEulerInverse family) *
            (sourceBandProjection lambda * detectorOperator owner *
              sourceSoninProjection lambda) := by
        rw [hForwardDetector, hReverseDetector]
      _ = _ := by noncomm_ring

/-- Actual physical boundary pair with the two correct band orientations
assembled on one `L2` target. -/
noncomputable def sourceActualBandFiniteEulerPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :=
  actualBandCommutatorPairData boundaryBasis
    (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor)
    (sourceBandProjection lambda) (sourceSoninProjection lambda)
    (normalizedFiniteEulerInverse family)
    (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))

theorem sourceActualBandFiniteEulerPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
    (sourceActualBandFiniteEulerPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor).traceProduct =
      sourceActualBandFiniteEulerPairedResponse owner lambda family := by
  apply actualBandCommutatorPairData_traceProduct_eq
  · calc
      (fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis
          boundaryBasis hfactor).traceProduct =
          fixedPhysicalCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) :=
        fixedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis
          boundaryBasis hfactor
          (radialSupportProjection_isStarProjection lambda).isIdempotentElem
          (radialSupportProjection_comp_sourceProlateRemainder lambda)
          (sourceProlateRemainder_comp_radialSupportProjection lambda)
      _ = _ := fixedPhysicalCommutator_eq_sourceCompressedCommutator
        owner lambda
  · exact (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  · simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  · simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda

theorem sourceActualBandFiniteEulerPairedResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (sourceActualBandFiniteEulerPairedResponse owner lambda family) := by
  rw [← sourceActualBandFiniteEulerPairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor]
  exact (sourceActualBandFiniteEulerPairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor).traceProduct_isTraceClassAlong

/-- The correctly oriented first jet is uniformly bounded by the fixed
physical boundary energy; the right side has no finite-prime family input. -/
theorem sourceActualBandFiniteEuler_ordinaryTrace_norm_le_fixedPhysicalEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
    let fixedPair :=
      fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis hfactor
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (sourceActualBandFiniteEulerPairedResponse owner lambda family)‖ ≤
      (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) +
        ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2 := by
  dsimp only
  let fixedPair :=
    fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor
  have hInner : ‖sourceSoninProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hBand : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hInverseAdjoint :
      ‖ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family)‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hInverse
  have hBandInverse :
      ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceBandProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hBand hInverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hForward :
      ‖sourceBandProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
          sourceSoninProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceBandProjection lambda ∘L
            normalizedFiniteEulerInverse family‖ *
          ‖sourceSoninProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hBandInverse hInner (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hInnerInverseAdjoint :
      ‖sourceSoninProjection lambda ∘L
          ContinuousLinearMap.adjoint
            (normalizedFiniteEulerInverse family)‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceSoninProjection lambda‖ *
          ‖ContinuousLinearMap.adjoint
            (normalizedFiniteEulerInverse family)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hInner hInverseAdjoint (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hReverse :
      ‖sourceSoninProjection lambda ∘L
          ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family) ∘L
          sourceBandProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceSoninProjection lambda ∘L
            ContinuousLinearMap.adjoint
              (normalizedFiniteEulerInverse family)‖ *
          ‖sourceBandProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hInnerInverseAdjoint hBand (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  rw [← sourceActualBandFiniteEulerPairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor]
  exact actualBandCommutatorPairData_ordinaryTrace_norm_le_sourceEnergy
    boundaryBasis fixedPair (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      hInner hForward hReverse

end CCM24FiniteSActualBandFirstJetTrace
end CCM25Concrete
end Source
end ConnesWeilRH
