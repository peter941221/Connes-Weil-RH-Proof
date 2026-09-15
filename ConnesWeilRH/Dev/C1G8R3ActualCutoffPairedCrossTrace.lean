/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffSignedRemainderLimit

/-!
# Paired actual-cutoff G8 leakage/source cross traces

The reverse source/leakage channel is the adjoint of the already controlled
leakage/source channel because the detector Gram is self-adjoint.  Its trace
therefore converges to the conjugate limit, and the paired channel has a real
ordinary-trace limit.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.C1G8AdjointShearGram
open Source.C1G8P1MetricChannels
open Source.C1G8P1EndpointOrientation
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance actualPairedCrossSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Keep the physical cutoff owner opaque while normalizing the Gram adjoint.
theorem g8MetricCutoffSourceLeakageCrossOperator_eq_adjoint
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    g8MetricCutoffSourceLeakageCrossOperator owner lambda family
        globalBasis sourceBasis n =
      (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
        globalBasis sourceBasis n).adjoint := by
  let C := (sourceInclusion lambda).adjoint ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := sourceInclusion lambda
  let E := g8MetricLeakageCoframe lambda family
  let D := detectorOperator owner
  have hD : D.adjoint = D := (detectorOperator_isSelfAdjoint owner).adjoint_eq
  change C.adjoint ∘L J.adjoint ∘L D ∘L E ∘L C =
    (C.adjoint ∘L E.adjoint ∘L D ∘L J ∘L C).adjoint
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    hD,
    ContinuousLinearMap.comp_assoc]

set_option maxHeartbeats 1000000 in
-- The full same-owner basis signature is inherited from the fixed source pair.
/-- The actual source/leakage ordered channel converges as the conjugate of
the leakage/source channel. -/
theorem tendsto_ordinaryTraceAlong_g8MetricSourceLeakageCross_actualCutoff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
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
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffSourceLeakageCrossOperator owner lambda family
          globalBasis sourceBasis n)) atTop
      (𝓝 (star (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
            g8SourceCompressedGlobalConvolution lambda owner.sourceTest)))) := by
  have hforward := tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis
  have hsequence :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffSourceLeakageCrossOperator owner lambda family
          globalBasis sourceBasis n)) =
      (fun n => star (ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
          globalBasis sourceBasis n))) := by
    funext n
    rw [g8MetricCutoffSourceLeakageCrossOperator_eq_adjoint,
      ordinaryTraceAlong_adjoint]
  rw [hsequence]
  simpa only [Complex.star_def] using
    (Complex.continuous_conj.tendsto _).comp hforward

set_option maxHeartbeats 1000000 in
-- The paired cross limit uses the same source basis and both literal channels.
/-- The sum of the two actual leakage/source cross channels has a real
ordinary-trace limit, equal to twice the real part of either ordered limit. -/
theorem tendsto_ordinaryTraceAlong_g8MetricPairedCross_actualCutoff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
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
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
            globalBasis sourceBasis n +
          g8MetricCutoffSourceLeakageCrossOperator owner lambda family
            globalBasis sourceBasis n)) atTop
      (𝓝 ((2 * (ordinaryTraceAlong sourceBasis
        ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
          (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
            g8SourceCompressedGlobalConvolution lambda owner.sourceTest)).re : ℝ) : ℂ)) := by
  let forwardLimit := ordinaryTraceAlong sourceBasis
    ((g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
      (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
        g8SourceCompressedGlobalConvolution lambda owner.sourceTest)
  have hforward := tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis
  have hbackward := tendsto_ordinaryTraceAlong_g8MetricSourceLeakageCross_actualCutoff
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis
  have hforwardTraceClass (n : ℕ) :=
    g8MetricCutoffLeakageSourceCrossOperator_isTraceClassAlong owner lambda
      family globalBasis sourceBasis n
  have hbackwardTraceClass (n : ℕ) :=
    g8MetricCutoffSourceLeakageCrossOperator_isTraceClassAlong owner lambda
      family globalBasis sourceBasis n
  have htraceSum :
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
            globalBasis sourceBasis n +
          g8MetricCutoffSourceLeakageCrossOperator owner lambda family
            globalBasis sourceBasis n)) =
      (fun n => ordinaryTraceAlong sourceBasis
          (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
            globalBasis sourceBasis n) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffSourceLeakageCrossOperator owner lambda family
            globalBasis sourceBasis n)) := by
    funext n
    exact ordinaryTraceAlong_add sourceBasis _ _
      (hforwardTraceClass n) (hbackwardTraceClass n)
  have hpaired := hforward.add hbackward
  rw [htraceSum]
  convert hpaired using 1
  rw [Complex.star_def, Complex.add_conj]

end Dev
end ConnesWeilRH
