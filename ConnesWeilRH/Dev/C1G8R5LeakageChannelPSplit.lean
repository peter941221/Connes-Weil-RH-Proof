/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffCrossTraceLimit
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# P2 split of the G8 leakage/source trace limit

The actual-cutoff leakage limit (record 1480) is the named-basis trace of the
sandwich `K† ∘L (-G†) ∘L K`, where `K` is the compressed global convolution
and `G = sourceBandGramResponse`. The committed band decomposition (record
1485) is `G = J₁ - R` with `J₁` the Sonin first jet and `R` the actual
nonlinear remainder. This leaf packages the resulting operator,
trace-class, and trace-level split of the limit:

```text
K† ∘L (-G†) ∘L K  =  (K† ∘L R† ∘L K)  -  (K† ∘L J₁† ∘L K)
     total                remainder            response
```

Every claim is linear-algebraic movement of committed identities: the
trace-class ownerships are `boundedSandwich` transports of the committed
`sourceThreeBranchSourcePairData` and
`sourceActualBandFiniteEulerSoninPairData` pair owners, and the remainder
ownership is their sum. No estimate, no positivity, and no identification of
either channel with `qw` is present or claimed; the pinned rho5 bridge
(record 1567) remains the consumer.
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
open Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance g8R5SplitSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The literal limit operator of the actual-cutoff leakage trace (record
1480): the adjoint-compressed band response between two global-convolution
compressions. -/
noncomputable def g8R5LeakageTotalChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
    (-(sourceBandGramResponse owner lambda family).adjoint) ∘L
      g8SourceCompressedGlobalConvolution lambda owner.sourceTest

/-- The compressed remainder (P2 sub-limit) channel: the same sandwich with
the actual nonlinear remainder response in the middle. -/
noncomputable def g8R5LeakageRemainderChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
    (sourceActualBandFiniteEulerRemainderResponse owner lambda family).adjoint ∘L
      g8SourceCompressedGlobalConvolution lambda owner.sourceTest

/-- The compressed Sonin-response channel: the same sandwich with the Sonin
first jet in the middle. -/
noncomputable def g8R5LeakageResponseChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
    (sourceActualBandFiniteEulerSoninResponse owner lambda family).adjoint ∘L
      g8SourceCompressedGlobalConvolution lambda owner.sourceTest

/-- The operator-level P2 split: `-(J₁ - R)† = R† - J₁†` sandwiched by `K`. -/
theorem g8R5LeakageChannel_eq_remainder_sub_response
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8R5LeakageTotalChannel owner lambda family =
      g8R5LeakageRemainderChannel owner lambda family -
        g8R5LeakageResponseChannel owner lambda family := by
  have hmid :
      -(sourceBandGramResponse owner lambda family).adjoint =
        (sourceActualBandFiniteEulerRemainderResponse owner lambda family).adjoint -
          (sourceActualBandFiniteEulerSoninResponse owner lambda family).adjoint := by
    have hadjoint_sub
        (A B : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
        (A - B)† = A† - B† := by
      apply ContinuousLinearMap.ext
      intro y
      exact ext_inner_right ℂ fun z => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    have h2 :
        (sourceBandGramResponse owner lambda family).adjoint =
          (sourceActualBandFiniteEulerSoninResponse owner lambda family).adjoint -
            (sourceActualBandFiniteEulerRemainderResponse owner lambda family).adjoint := by
      rw [sourceBandGramResponse_eq_soninFirstJet_sub_remainder, hadjoint_sub]
    rw [h2, neg_sub]
  apply ContinuousLinearMap.ext
  intro x
  simp [g8R5LeakageTotalChannel, g8R5LeakageRemainderChannel,
    g8R5LeakageResponseChannel, hmid]

/-- The total channel is trace-class along the source basis: the committed
three-branch pair owns `G`, so `(-1) • G† = -G†` owns the literal middle
factor, and the bounded sandwich transports the pair. -/
theorem isTraceClassAlong_g8R5LeakageTotalChannel
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
    IsTraceClassAlong sourceBasis
      (g8R5LeakageTotalChannel owner lambda family) := by
  set hfactor :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda with hfactorDef
  set basePair := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor with hbasePairDef
  have htp : basePair.traceProduct = sourceBandGramResponse owner lambda family := by
    rw [hbasePairDef]
    rw [sourceThreeBranchSourcePairData_traceProduct_eq]
  set pair := basePair.swap.smulRight (-1 : ℂ) with hpairDef
  have hpairtp :
      pair.traceProduct = -(sourceBandGramResponse owner lambda family).adjoint := by
    rw [hpairDef, BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, htp]
    simp
  have h :=
    BasisHilbertSchmidtPairData.boundedSandwich_isTraceClassAlong
      boundaryBasis pair
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest)
  rw [hpairtp] at h
  simpa [g8R5LeakageTotalChannel] using h

/-- The compressed Sonin-response channel is trace-class along the source
basis: the committed Sonin pair owns `J₁`, its swap owns `J₁†`, and the
bounded sandwich transports the pair. -/
theorem isTraceClassAlong_g8R5LeakageResponseChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    IsTraceClassAlong sourceBasis
      (g8R5LeakageResponseChannel owner lambda family) := by
  set hfactor :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda with hfactorDef
  set dataJ := sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor with hdataJDef
  have htpJ :
      dataJ.traceProduct = sourceActualBandFiniteEulerSoninResponse
        owner lambda family := by
    rw [hdataJDef]
    rw [sourceActualBandFiniteEulerSoninPairData_traceProduct_eq]
  set pairJ := dataJ.swap with hpairJDef
  have hpairJtp :
      pairJ.traceProduct =
        (sourceActualBandFiniteEulerSoninResponse owner lambda family).adjoint := by
    rw [hpairJDef, BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, htpJ]
  have h :=
    BasisHilbertSchmidtPairData.boundedSandwich_isTraceClassAlong
      pairedBoundaryBasis pairJ
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest)
  rw [hpairJtp] at h
  simpa [g8R5LeakageResponseChannel] using h

/-- The compressed remainder channel is trace-class: it is the sum of the
total and response channels. -/
theorem isTraceClassAlong_g8R5LeakageRemainderChannel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    IsTraceClassAlong sourceBasis
      (g8R5LeakageRemainderChannel owner lambda family) := by
  have hop :
      g8R5LeakageRemainderChannel owner lambda family =
        g8R5LeakageTotalChannel owner lambda family +
          g8R5LeakageResponseChannel owner lambda family := by
    rw [g8R5LeakageChannel_eq_remainder_sub_response]
    abel
  rw [hop]
  exact isTraceClassAlong_add sourceBasis _ _
    (isTraceClassAlong_g8R5LeakageTotalChannel owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis)
    (isTraceClassAlong_g8R5LeakageResponseChannel owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis)

/-- The trace-level P2 split of the leakage limit: the named-basis trace of
the total channel is the remainder-channel trace minus the response-channel
trace. -/
theorem g8R5LeakageChannelTrace_split
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (g8R5LeakageTotalChannel owner lambda family) =
      ordinaryTraceAlong sourceBasis
          (g8R5LeakageRemainderChannel owner lambda family) -
        ordinaryTraceAlong sourceBasis
          (g8R5LeakageResponseChannel owner lambda family) := by
  rw [g8R5LeakageChannel_eq_remainder_sub_response]
  exact ordinaryTraceAlong_sub sourceBasis
    (g8R5LeakageRemainderChannel owner lambda family)
    (g8R5LeakageResponseChannel owner lambda family)
    (isTraceClassAlong_g8R5LeakageRemainderChannel owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis)
    (isTraceClassAlong_g8R5LeakageResponseChannel owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis)

set_option maxHeartbeats 1000000 in
/-- The P2-split form of the actual-cutoff leakage limit: the same truncated
source-compressed physical cutoff converges to the difference of the two
named channel traces. -/
theorem tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff_p2Split
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8MetricCutoffLeakageSourceCrossOperator owner lambda family
          globalBasis sourceBasis n)) atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
          (g8R5LeakageRemainderChannel owner lambda family) -
            ordinaryTraceAlong sourceBasis
              (g8R5LeakageResponseChannel owner lambda family))) := by
  have h :=
    tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis
  have hsp :=
    g8R5LeakageChannelTrace_split owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis
  rw [← hsp]
  exact h

end Dev
end ConnesWeilRH
