/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalBoundaryDifference

/-!
# Physical boundary cycle for the Gate response

Proof 729 writes the Gate response as one signed difference through the fixed
three-branch commutator.  This file cycles both terms through the already
owned common Hilbert--Schmidt factors and recombines them on the physical
boundary carrier.  The resulting middle operator is

```text
endpoint o sourceInclusion^dagger
  - sourceInclusion o forward^dagger.
```

The cycle is justified by Hilbert--Schmidt summability on both cuts.  No raw
infinite-dimensional trace cycle, branchwise norm, uniform bound, finite-S
sign, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalBoundaryCycle

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalBoundaryDifference
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem rectangularCycleDifference_factor
    {H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (left right : H →L[ℂ] G) (endpoint inclusion forward : K →L[ℂ] H) :
    (right ∘L endpoint) ∘L (left ∘L inclusion)† -
        (right ∘L inclusion) ∘L (left ∘L forward)† =
      right ∘L
        (endpoint ∘L inclusion† - inclusion ∘L forward†) ∘L left† := by
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]

private theorem pairCycledDifference_factor
    {ι κ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {baseBasis : HilbertBasis ι ℂ H}
    {sourceBasis : HilbertBasis κ ℂ K}
    (base : BasisHilbertSchmidtPairData (G := G) baseBasis)
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (endpoint inclusion forward : K →L[ℂ] H)
    (hfirstLeft : first.left = base.left ∘L inclusion)
    (hfirstRight : first.right = base.right ∘L endpoint)
    (hsecondLeft : second.left = base.left ∘L forward)
    (hsecondRight : second.right = base.right ∘L inclusion) :
    first.right ∘L first.left† - second.right ∘L second.left† =
      base.right ∘L
        (endpoint ∘L inclusion† - inclusion ∘L forward†) ∘L base.left† := by
  calc
    first.right ∘L first.left† - second.right ∘L second.left† =
        (base.right ∘L endpoint) ∘L (base.left ∘L inclusion)† -
          (base.right ∘L inclusion) ∘L (base.left ∘L forward)† :=
      congrArg₂ (fun left right : G →L[ℂ] G => left - right)
        (congrArg₂ (fun right left : K →L[ℂ] G => right ∘L left†)
          hfirstRight hfirstLeft)
        (congrArg₂ (fun right left : K →L[ℂ] G => right ∘L left†)
          hsecondRight hsecondLeft)
    _ = base.right ∘L
        (endpoint ∘L inclusion† - inclusion ∘L forward†) ∘L base.left† :=
      rectangularCycleDifference_factor base.left base.right endpoint inclusion
        forward

private theorem cyclicProduct_isTraceClassAlong
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    IsTraceClassAlong targetBasis (data.right ∘L data.left†) := by
  let cycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := data.right†
      right := data.left†
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.right data.right_summable_normSq
      right_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.left data.left_summable_normSq }
  have hcycled := cycled.traceProduct_isTraceClassAlong
  have hproduct : cycled.traceProduct = data.right ∘L data.left† := by
    dsimp only [cycled, BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [hproduct] at hcycled
  exact hcycled

private theorem cycledSandwich_isTraceClassAlong
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (middle : H →L[ℂ] H) :
    IsTraceClassAlong targetBasis
      (data.right ∘L middle ∘L data.left†) := by
  let cycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := data.right†
      right := middle ∘L data.left†
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.right data.right_summable_normSq
      right_summable_normSq :=
        summable_normSq_postcomp targetBasis (data.left†) middle
          (BasisHilbertSchmidtPairData.summable_adjoint_normSq
            sourceBasis targetBasis data.left data.left_summable_normSq) }
  have hcycled := cycled.traceProduct_isTraceClassAlong
  have hproduct : cycled.traceProduct =
      data.right ∘L middle ∘L data.left† := by
    dsimp only [cycled, BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [hproduct] at hcycled
  exact hcycled

/-- The complete ambient coframe difference produced by the rectangular
cycle.  It keeps endpoint and reverse-forward orientations in one operator. -/
noncomputable def sourceGatePhysicalCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardEndpointCoframe lambda family ∘L
      (sourceInclusion lambda)† -
    sourceInclusion lambda ∘L
      (sourceActualBandForwardCoframe lambda family)†

/-- The reverse first-jet Hilbert--Schmidt pair before its minus sign is
inserted at the operator level. -/
noncomputable def sourceActualBandReverseForwardPairData
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis :=
  BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceActualBandForwardCoframe lambda family)
    (sourceInclusion lambda)

theorem sourceActualBandReverseForwardPairData_traceProduct_eq
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandReverseForwardPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        (sourceActualBandForwardCoframe lambda family)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          sourceInclusion lambda := by
  rw [sourceActualBandReverseForwardPairData,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]

private theorem lowerFactorGaugedResponse_eq_pairTraceDifference
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    lowerFactorGaugedActualBandCompletedRelativeResponse owner lambda family =
      (sourceActualBandForwardEndpointPairData owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).traceProduct -
      (sourceActualBandReverseForwardPairData owner lambda family a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).traceProduct := by
  rw [sourceActualBandForwardEndpointPairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    sourceActualBandReverseForwardPairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor]
  exact lowerFactorGaugedResponse_eq_completePhysicalBoundaryDifference
    owner lambda family

/-- The Gate response after both legal Hilbert--Schmidt cycles have been
recombined on the one common physical boundary carrier. -/
noncomputable def sourceGatePhysicalBoundaryCycleResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L sourceGatePhysicalCoframeDifference lambda family ∘L
    base.left†

/-- The boundary-side cycle is trace legal in the same common boundary basis. -/
theorem sourceGatePhysicalBoundaryCycleResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalBoundaryCycleResponse
        (ι := ι) (κ := κ) (τ := τ) (ιr := ιr) (κr := κr) (τr := τr)
        (ν := ν) owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L sourceGatePhysicalCoframeDifference lambda family ∘L
      base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceGatePhysicalCoframeDifference lambda family)

private theorem ordinaryTraceAlong_pairDifference_eq_cycledDifference
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    ordinaryTraceAlong sourceBasis
        (first.traceProduct - second.traceProduct) =
      ordinaryTraceAlong targetBasis
        ((first.right ∘L first.left†) -
          (second.right ∘L second.left†)) := by
  have hfirstBoundary :=
    cyclicProduct_isTraceClassAlong sourceBasis targetBasis first
  have hsecondBoundary :=
    cyclicProduct_isTraceClassAlong sourceBasis targetBasis second
  calc
    ordinaryTraceAlong sourceBasis
        (first.traceProduct - second.traceProduct) =
        ordinaryTraceAlong sourceBasis first.traceProduct -
          ordinaryTraceAlong sourceBasis second.traceProduct :=
      CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
        sourceBasis _ _ first.traceProduct_isTraceClassAlong
          second.traceProduct_isTraceClassAlong
    _ = ordinaryTraceAlong targetBasis
          (first.right ∘L first.left†) -
        ordinaryTraceAlong targetBasis
          (second.right ∘L second.left†) :=
      congrArg₂ (fun left right : ℂ => left - right)
        (first.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis)
        (second.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis)
    _ = ordinaryTraceAlong targetBasis
          ((first.right ∘L first.left†) -
            (second.right ∘L second.left†)) :=
      (CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
        targetBasis _ _ hfirstBoundary hsecondBoundary).symm

private theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryCycle_expanded
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            hfactor).right ∘L
          sourceGatePhysicalCoframeDifference lambda family ∘L
          (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            hfactor).left†) := by
  let first := sourceActualBandForwardEndpointPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let second := sourceActualBandReverseForwardPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hgate :
      lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family =
        first.traceProduct - second.traceProduct := by
    dsimp only [first, second]
    exact lowerFactorGaugedResponse_eq_pairTraceDifference owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hfirstLeft : first.left = base.left ∘L sourceInclusion lambda := by
    dsimp only [first, sourceActualBandForwardEndpointPairData, base]
    exact boundedPrecompAddRight_left_eq boundaryBasis sourceBasis _ _ _ _
  have hfirstRight : first.right =
      base.right ∘L sourceActualBandForwardEndpointCoframe lambda family := by
    dsimp only [first, sourceActualBandForwardEndpointPairData, base]
    rw [boundedPrecompAddRight_right_eq]
    rfl
  have hsecondLeft : second.left =
      base.left ∘L sourceActualBandForwardCoframe lambda family := by
    rfl
  have hsecondRight : second.right =
      base.right ∘L sourceInclusion lambda := by
    rfl
  have hboundaryOperator :
      first.right ∘L first.left† - second.right ∘L second.left† =
        base.right ∘L sourceGatePhysicalCoframeDifference lambda family ∘L
          base.left† := by
    rw [sourceGatePhysicalCoframeDifference]
    exact pairCycledDifference_factor base first second
      (sourceActualBandForwardEndpointCoframe lambda family)
      (sourceInclusion lambda) (sourceActualBandForwardCoframe lambda family)
      hfirstLeft hfirstRight hsecondLeft hsecondRight
  calc
    ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
        ordinaryTraceAlong sourceBasis
          (first.traceProduct - second.traceProduct) :=
      congrArg (ordinaryTraceAlong sourceBasis) hgate
    _ = ordinaryTraceAlong boundaryBasis
          ((first.right ∘L first.left†) -
            (second.right ∘L second.left†)) :=
      ordinaryTraceAlong_pairDifference_eq_cycledDifference
        sourceBasis boundaryBasis first second
    _ = ordinaryTraceAlong boundaryBasis
          (base.right ∘L sourceGatePhysicalCoframeDifference lambda family ∘L
            base.left†) :=
      congrArg (ordinaryTraceAlong boundaryBasis) hboundaryOperator

/-- The Gate trace is exactly the trace of one signed operator on the common
physical boundary carrier. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryCycle
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCycleResponse
          (ι := ι) (κ := κ) (τ := τ) (ιr := ιr) (κr := κr) (τr := τr)
          (ν := ν) owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis hfactor) := by
  simpa only [sourceGatePhysicalBoundaryCycleResponse] using
    ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryCycle_expanded
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor

/-- A Gate 3U trace-norm bound is exactly a bound for the single cycled
physical-boundary operator. -/
theorem lowerFactorGaugedResponse_trace_norm_le_iff_boundaryCycle
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ) :
    ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound ↔
      ‖ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCycleResponse
          (ι := ι) (κ := κ) (τ := τ) (ιr := ιr) (κr := κr) (τr := τr)
          (ν := ν) owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis hfactor)‖ ≤ bound := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryCycle]

end CCM24FiniteSGatePhysicalBoundaryCycle
end CCM25Concrete
end Source
end ConnesWeilRH
