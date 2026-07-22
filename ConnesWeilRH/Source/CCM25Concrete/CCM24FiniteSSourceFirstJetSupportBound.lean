/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualFirstJetSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder

/-!
# Source-Sonin support bound for the actual finite-Euler first jet

The actual paired first jet is absorbed by the source Sonin projection on
both sides.  Its pullback through the isometric Sonin inclusion therefore has
the same ordinary trace as the ambient response.  The carrier change is
proved through genuine Hilbert--Schmidt cycles, not an appeal to abstract
basis independence.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSourceFirstJetSupportBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInverseMetric
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualFirstJetSupportBound
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
-- Normalizing the generic noncommutative five-factor expression is costly.
private theorem actualBandDetectorPairedResponse_mul_inner
    {A : Type*} [Ring A]
    (band inner detector transport transportAdjoint : A)
    (hInner : inner * inner = inner) :
    actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint * inner =
      actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint := by
  unfold actualBandDetectorPairedResponse
  calc
    (inner * detector * band * transport * inner +
          inner * transportAdjoint * band * detector * inner) * inner =
        inner * detector * band * transport * (inner * inner) +
          inner * transportAdjoint * band * detector * (inner * inner) := by
      noncomm_ring
    _ = _ := by rw [hInner]

set_option maxHeartbeats 1000000 in
-- Normalizing the generic noncommutative five-factor expression is costly.
private theorem inner_mul_actualBandDetectorPairedResponse
    {A : Type*} [Ring A]
    (band inner detector transport transportAdjoint : A)
    (hInner : inner * inner = inner) :
    inner * actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint =
      actualBandDetectorPairedResponse band inner detector transport
        transportAdjoint := by
  unfold actualBandDetectorPairedResponse
  calc
    inner * (inner * detector * band * transport * inner +
          inner * transportAdjoint * band * detector * inner) =
        (inner * inner) * detector * band * transport * inner +
          (inner * inner) * transportAdjoint * band * detector * inner := by
      noncomm_ring
    _ = _ := by rw [hInner]

/-- The ambient paired first jet is supported on the source Sonin subspace on
the right. -/
theorem sourceActualBandFiniteEulerPairedResponse_comp_sourceSoninProjection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerPairedResponse owner lambda family ∘L
        sourceSoninProjection lambda =
      sourceActualBandFiniteEulerPairedResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerPairedResponse_eq_rawDetector]
  simpa only [ContinuousLinearMap.mul_def] using
    actualBandDetectorPairedResponse_mul_inner
      (sourceBandProjection lambda) (sourceSoninProjection lambda)
      (detectorOperator owner) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem

/-- The ambient paired first jet is supported on the source Sonin subspace on
the left. -/
theorem sourceSoninProjection_comp_sourceActualBandFiniteEulerPairedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceActualBandFiniteEulerPairedResponse owner lambda family =
      sourceActualBandFiniteEulerPairedResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerPairedResponse_eq_rawDetector]
  simpa only [ContinuousLinearMap.mul_def] using
    inner_mul_actualBandDetectorPairedResponse
      (sourceBandProjection lambda) (sourceSoninProjection lambda)
      (detectorOperator owner) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem

set_option maxHeartbeats 2000000 in
-- Both traces are cycled through the common physical pair carrier.  This
-- keeps every interchange behind explicit Hilbert--Schmidt summability.
/-- Pullback through the source Sonin inclusion preserves the ordinary trace
of the actual paired first jet. -/
theorem sourceActualBandFiniteEulerSoninTrace_eq_ambientTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family) =
      ordinaryTraceAlong globalBasis
        (sourceActualBandFiniteEulerPairedResponse owner lambda family) := by
  let J := sourceInclusion lambda
  let P := sourceSoninProjection lambda
  let ambientPair :=
    sourceActualBandFiniteEulerPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor
  let sourcePair :=
    BasisHilbertSchmidtPairData.boundedPrecomp pairedBoundaryBasis sourceBasis
      ambientPair J J
  have hAmbientProduct : ambientPair.traceProduct =
      sourceActualBandFiniteEulerPairedResponse owner lambda family := by
    dsimp only [ambientPair]
    exact sourceActualBandFiniteEulerPairData_traceProduct_eq owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor
  have hSourceProduct : sourcePair.traceProduct =
      sourceActualBandFiniteEulerSoninResponse owner lambda family := by
    dsimp only [sourcePair]
    rw [BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
      hAmbientProduct]
    rfl
  have hProjection : J ∘L J.adjoint = P := by
    dsimp only [J, P]
    exact sourceInclusion_comp_adjoint lambda
  have hRightProjection : Summable fun i =>
      ‖(ambientPair.right ∘L P) (globalBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp globalBasis pairedBoundaryBasis globalBasis
      ambientPair.right P ambientPair.right_summable_normSq
  have hSourceCycle :=
    sourcePair.ordinaryTraceAlong_traceProduct_eq_cyclic pairedBoundaryBasis
  have hAmbientCycle :=
    BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
      globalBasis
      pairedBoundaryBasis ambientPair.left (ambientPair.right ∘L P)
      ambientPair.left_summable_normSq hRightProjection
  rw [← hSourceProduct]
  calc
    ordinaryTraceAlong sourceBasis sourcePair.traceProduct =
        ordinaryTraceAlong pairedBoundaryBasis
          (sourcePair.right ∘L sourcePair.left.adjoint) := hSourceCycle
    _ = ordinaryTraceAlong pairedBoundaryBasis
        ((ambientPair.right ∘L P) ∘L ambientPair.left.adjoint) := by
      apply congrArg (ordinaryTraceAlong pairedBoundaryBasis)
      dsimp only [sourcePair,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
      rw [ContinuousLinearMap.adjoint_comp]
      calc
        ((ambientPair.right ∘L J) ∘L
              (J.adjoint ∘L ambientPair.left.adjoint)) =
            (ambientPair.right ∘L (J ∘L J.adjoint)) ∘L
              ambientPair.left.adjoint := by
          apply ContinuousLinearMap.ext
          intro u
          rfl
        _ = (ambientPair.right ∘L P) ∘L ambientPair.left.adjoint := by
          rw [hProjection]
    _ = ordinaryTraceAlong globalBasis
        (ambientPair.left.adjoint ∘L (ambientPair.right ∘L P)) :=
      hAmbientCycle.symm
    _ = ordinaryTraceAlong globalBasis (ambientPair.traceProduct ∘L P) := by
      apply congrArg (ordinaryTraceAlong globalBasis)
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = ordinaryTraceAlong globalBasis
        (sourceActualBandFiniteEulerPairedResponse owner lambda family ∘L P) := by
      rw [hAmbientProduct]
    _ = ordinaryTraceAlong globalBasis
        (sourceActualBandFiniteEulerPairedResponse owner lambda family) := by
      rw [show P = sourceSoninProjection lambda by rfl,
        sourceActualBandFiniteEulerPairedResponse_comp_sourceSoninProjection]

/-- The actual first jet on the source Sonin carrier inherits the same
finite-family-uniform support bound as its ambient owner. -/
theorem sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family)‖ ≤
      (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  rw [sourceActualBandFiniteEulerSoninTrace_eq_ambientTrace owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]
  exact sourceActualBandFiniteEulerPairedTrace_norm_le_supportEnergy owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor

end CCM24FiniteSSourceFirstJetSupportBound
end CCM25Concrete
end Source
end ConnesWeilRH
