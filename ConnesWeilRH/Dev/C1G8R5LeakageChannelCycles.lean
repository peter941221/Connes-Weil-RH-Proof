/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R5LeakageChannelPSplit

/-!
# Boundary-carrier cycles of the named leakage channels

The P2 split (record 1569) named the remainder and response channels as
sandwiches of the source band response between two global-convolution
compressions. Each channel trace is carried by a committed Hilbert-Schmidt
pair owner, so its named-basis trace cycles to the pair's factor carrier by
`ordinaryTraceAlong_traceProduct_eq_cyclic`:

```text
tr_source (K^dag J1^dag K)   =  tr_{actualBandPairCarrier}(...)
tr_source (K^dag (-G^dag) K) =  tr_{commonBoundaryCarrier}(...)
```

The operands are the sandwiched pair legs transported to the factor space -
the same carrier where the boundary-leg machinery of records 1492/1493/1495
lives, so the cycles are the formal interface through which the rho5
combined-row producer may consume the channels at the boundary side
(map 042 IN/OUT split). Pure cyclicity bookkeeping: no estimate, no sign,
no identification with `qw` components.
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

noncomputable local instance g8R5CycleSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
/-- The response channel trace cycles onto the actual-band pair carrier. -/
theorem ordinaryTraceAlong_g8R5LeakageResponseChannel_eq_cyclic
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
        (g8R5LeakageResponseChannel owner lambda family) =
      ordinaryTraceAlong pairedBoundaryBasis
        ((((sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
              pairedBoundaryBasis sourceBasis
              (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)).left
              ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
            ((sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
                negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                pairedBoundaryBasis sourceBasis
                (sourceProlateHilbertSchmidtFactor_summable_all_scales
                  globalBasis lambda)).right
                ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint)) := by
  set hfactor :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda with hfactorDef
  set dataJ := sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor with hdataJDef
  set pairJ := dataJ.swap.boundedSandwich pairedBoundaryBasis
    (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint
    (g8SourceCompressedGlobalConvolution lambda owner.sourceTest) with hpJDef
  have hcyc := BasisHilbertSchmidtPairData.ordinaryTraceAlong_traceProduct_eq_cyclic
    pairedBoundaryBasis pairJ
  have htp : pairJ.traceProduct =
      g8R5LeakageResponseChannel owner lambda family := by
    rw [hpJDef, BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hdataJDef,
      sourceActualBandFiniteEulerSoninPairData_traceProduct_eq,
      g8R5LeakageResponseChannel]
  rw [htp] at hcyc
  have h1 : pairJ.right =
      dataJ.left ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest := rfl
  have h2 : pairJ.left = dataJ.right ∘L
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint.adjoint := rfl
  rw [h1, h2, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] at hcyc
  simpa [hdataJDef, hfactorDef] using hcyc

set_option maxHeartbeats 1000000 in
/-- The total channel trace cycles onto the common boundary carrier. The
minus sign of the signed commutator pair is carried by the cycled operand as
an operator negation on the boundary endo. -/
theorem ordinaryTraceAlong_g8R5LeakageTotalChannel_eq_cyclic
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
    ordinaryTraceAlong sourceBasis (g8R5LeakageTotalChannel owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        (-(((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                sourceBasis
                (sourceProlateHilbertSchmidtFactor_summable_all_scales
                  globalBasis lambda)).left
                ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
              ((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                  negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                  reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                  sourceBasis
                  (sourceProlateHilbertSchmidtFactor_summable_all_scales
                    globalBasis lambda)).right
                  ∘L g8SourceCompressedGlobalConvolution lambda
                    owner.sourceTest).adjoint)) := by
  set hfactor :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda with hfactorDef
  set baseG := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor with hbaseGDef
  set pairU := baseG.swap.boundedSandwich boundaryBasis
    (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint
    (g8SourceCompressedGlobalConvolution lambda owner.sourceTest) with hpUDef
  have hcycU := BasisHilbertSchmidtPairData.ordinaryTraceAlong_traceProduct_eq_cyclic
    boundaryBasis pairU
  have htpU : pairU.traceProduct =
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint ∘L
        (sourceBandGramResponse owner lambda family).adjoint ∘L
          g8SourceCompressedGlobalConvolution lambda owner.sourceTest := by
    rw [hpUDef, BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hbaseGDef,
      sourceThreeBranchSourcePairData_traceProduct_eq]
  have hch : g8R5LeakageTotalChannel owner lambda family = -(pairU.traceProduct) := by
    rw [htpU, g8R5LeakageTotalChannel]
    simp
  have h1 : pairU.right =
      baseG.left ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest := rfl
  have h2 : pairU.left = baseG.right ∘L
      (g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint.adjoint := rfl
  rw [h1, h2, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.adjoint_comp] at hcycU
  have hsrc : ordinaryTraceAlong sourceBasis (-(pairU.traceProduct)) =
      -(ordinaryTraceAlong sourceBasis pairU.traceProduct) := by
    rw [ordinaryTraceAlong, ordinaryTraceAlong]
    simp only [ContinuousLinearMap.neg_apply, tsum_neg, inner_neg_right]
  have hbnd : ordinaryTraceAlong boundaryBasis
      (-(((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                sourceBasis
                (sourceProlateHilbertSchmidtFactor_summable_all_scales
                  globalBasis lambda)).left
                ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
              ((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                  negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                  reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                  sourceBasis
                  (sourceProlateHilbertSchmidtFactor_summable_all_scales
                    globalBasis lambda)).right
                  ∘L g8SourceCompressedGlobalConvolution lambda
                    owner.sourceTest).adjoint)) =
      -(ordinaryTraceAlong boundaryBasis
          (((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                    sourceBasis
                    (sourceProlateHilbertSchmidtFactor_summable_all_scales
                      globalBasis lambda)).left
                    ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
                  ((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                      sourceBasis
                      (sourceProlateHilbertSchmidtFactor_summable_all_scales
                        globalBasis lambda)).right
                      ∘L g8SourceCompressedGlobalConvolution lambda
                        owner.sourceTest).adjoint)) := by
    rw [ordinaryTraceAlong, ordinaryTraceAlong]
    simp only [ContinuousLinearMap.neg_apply, tsum_neg, inner_neg_right]
  rw [hch, hsrc, hbnd]
  exact congrArg Neg.neg hcycU

set_option maxHeartbeats 1000000 in
/-- The remainder channel trace, cycled: the boundary-carrier total cycle plus
the pair-carrier response cycle (scalar combination of the two carriers'
traces; record 1569's trace split transported through both cycles). -/
theorem ordinaryTraceAlong_g8R5LeakageRemainderChannel_eq_cyclic_pairSum
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
    ordinaryTraceAlong sourceBasis (g8R5LeakageRemainderChannel owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        (-(((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                sourceBasis
                (sourceProlateHilbertSchmidtFactor_summable_all_scales
                  globalBasis lambda)).left
                ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
              ((sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
                  negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                  reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                  sourceBasis
                  (sourceProlateHilbertSchmidtFactor_summable_all_scales
                    globalBasis lambda)).right
                  ∘L g8SourceCompressedGlobalConvolution lambda
                    owner.sourceTest).adjoint)) +
      ordinaryTraceAlong pairedBoundaryBasis
        ((((sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
              negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
              pairedBoundaryBasis sourceBasis
              (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda)).left
              ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest) ∘L
            ((sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
                negativeBasis positiveBasis outputBasis reflectedNegativeBasis
                reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
                pairedBoundaryBasis sourceBasis
                (sourceProlateHilbertSchmidtFactor_summable_all_scales
                  globalBasis lambda)).right
                ∘L g8SourceCompressedGlobalConvolution lambda owner.sourceTest).adjoint)) := by
  have hsplit := g8R5LeakageChannelTrace_split owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis
  have htotal := ordinaryTraceAlong_g8R5LeakageTotalChannel_eq_cyclic owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis sourceBasis
  have hresp := ordinaryTraceAlong_g8R5LeakageResponseChannel_eq_cyclic owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis
  have hadd : ordinaryTraceAlong sourceBasis
      (g8R5LeakageRemainderChannel owner lambda family) =
      ordinaryTraceAlong sourceBasis (g8R5LeakageTotalChannel owner lambda family) +
        ordinaryTraceAlong sourceBasis (g8R5LeakageResponseChannel owner lambda family) := by
    rw [hsplit]
    abel
  rw [hadd, htotal, hresp]

end Dev
end ConnesWeilRH
