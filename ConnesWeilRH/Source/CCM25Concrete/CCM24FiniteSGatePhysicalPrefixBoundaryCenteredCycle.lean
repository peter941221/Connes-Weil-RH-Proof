/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalBoundaryCenteredCycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixBoundaryCycle

/-!
# Centered common-boundary cycle for the finite physical Gate prefix

Proof 738 cycles the ordered source prefix through the common physical
Hilbert--Schmidt owner.  Its middle operator still contains the fixed source
block `J P_N J^dagger`.  This file proves that the fixed block has exactly zero
boundary trace for every bounded cutoff, then retains only the two genuine
family-dependent off-diagonal corners.

No cutoff is commuted through an endpoint, forward coframe, inclusion, or
boundary factor.  No uniform estimate, finite-S sign, Burnol identity, or RH
premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixBoundaryCenteredCycle

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSGatePhysicalBoundaryCenteredCycle
open CCM24FiniteSGatePhysicalPrefixBoundaryCycle
open CCM24FiniteSGatePhysicalPrefixRootPairing
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRectangularTailFactorization
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The family-independent source block with the literal finite prefix kept
between the inclusion and its adjoint. -/
noncomputable def sourceGatePhysicalPrefixProjectionCoframe
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceInclusion lambda ∘L basisPrefixProjection sourceBasis N ∘L
    (sourceInclusion lambda)†

/-- The two genuine family-dependent prefix corners after the fixed source
block is separated, but before its boundary trace is removed. -/
noncomputable def sourceGatePhysicalPrefixCenteredCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceEndpointCancellationResidual lambda family ∘L
      basisPrefixProjection sourceBasis N ∘L (sourceInclusion lambda)† -
    sourceInclusion lambda ∘L basisPrefixProjection sourceBasis N ∘L
      (sourceActualBandForwardCoframe lambda family)†

/-- Proof 738's finite-prefix middle operator is its fixed source block plus
the centered residual/forward difference. -/
theorem sourceGatePhysicalPrefixCoframeDifference_eq_projection_add_centered
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceGatePhysicalPrefixCoframeDifference
        lambda family sourceBasis N =
      sourceGatePhysicalPrefixProjectionCoframe lambda sourceBasis N +
        sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N := by
  rw [sourceGatePhysicalPrefixCoframeDifference,
    sourceGatePhysicalPrefixProjectionCoframe,
    sourceGatePhysicalPrefixCenteredCoframeDifference,
    sourceEndpointCancellationResidual_eq_endpoint_sub_inclusion]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  abel

/-- The source-Sonin left compression of the centered prefix is the negative
reverse-forward corner. -/
theorem sourceSoninProjection_comp_prefixCenteredCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceSoninProjection lambda ∘L
        sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N =
      -(sourceInclusion lambda ∘L basisPrefixProjection sourceBasis N ∘L
        (sourceActualBandForwardCoframe lambda family)†) := by
  apply ContinuousLinearMap.ext
  intro x
  have hresidual := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator
        (basisPrefixProjection sourceBasis N
          (((sourceInclusion lambda)†) x)))
    (sourceSoninProjection_comp_sourceEndpointCancellationResidual_eq_zero
      lambda family)
  have hinclusion := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator
        (basisPrefixProjection sourceBasis N
          (((sourceActualBandForwardCoframe lambda family)†) x)))
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [sourceGatePhysicalPrefixCenteredCoframeDifference,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply,
    map_sub] at hresidual hinclusion ⊢
  rw [hresidual, hinclusion]
  simp

/-- The right source-Sonin compression of the centered prefix is the endpoint
residual corner. -/
theorem prefixCenteredCoframeDifference_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N ∘L sourceSoninProjection lambda =
      sourceEndpointCancellationResidual lambda family ∘L
        basisPrefixProjection sourceBasis N ∘L (sourceInclusion lambda)† := by
  rw [← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  have hinclusion := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda =>
      operator (((sourceInclusion lambda)†) x))
    (sourceInclusion_adjoint_comp_self lambda)
  have hforward := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda =>
      operator (((sourceInclusion lambda)†) x))
    (sourceActualBandForwardCoframe_adjoint_comp_sourceInclusion_eq_zero
      lambda family)
  simp only [sourceGatePhysicalPrefixCenteredCoframeDifference,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] at hinclusion hforward ⊢
  rw [hinclusion, hforward]
  simp

/-- The centered finite-prefix coframe has no source-Sonin diagonal corner. -/
theorem prefixCenteredCoframeDifference_sourceSonin_corner_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    sourceSoninProjection lambda ∘L
        sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N ∘L sourceSoninProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hright := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
    (prefixCenteredCoframeDifference_comp_sourceSoninProjection
      lambda family sourceBasis N)
  have hleft := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator
        (basisPrefixProjection sourceBasis N
          (((sourceInclusion lambda)†) x)))
    (sourceSoninProjection_comp_sourceEndpointCancellationResidual_eq_zero
      lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hright hleft ⊢
  rw [hright, hleft]

/-- The centered finite-prefix coframe also has no complementary diagonal
corner; the cutoff remains entirely on the source carrier. -/
theorem prefixCenteredCoframeDifference_complement_corner_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) = 0 := by
  let complement :=
    ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda
  have hinclusionAdjoint :
      (sourceInclusion lambda)† ∘L complement = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have habsorb := congrArg
      (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        operator x)
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
    simp only [complement, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, map_sub] at habsorb ⊢
    rw [habsorb, sub_self]
  have hcomplementInclusion :
      complement ∘L sourceInclusion lambda = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have habsorb := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x)
      (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
    simp only [complement, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply] at habsorb ⊢
    rw [habsorb, sub_self]
  apply ContinuousLinearMap.ext
  intro x
  have hright := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator x) hinclusionAdjoint
  have hleft := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator
        (basisPrefixProjection sourceBasis N
          (((sourceActualBandForwardCoframe lambda family)†)
            (complement x))))
    hcomplementInclusion
  change complement
      (sourceGatePhysicalPrefixCenteredCoframeDifference
        lambda family sourceBasis N (complement x)) = 0
  simp only [sourceGatePhysicalPrefixCenteredCoframeDifference,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub, ContinuousLinearMap.zero_apply] at hright hleft ⊢
  rw [hright, map_zero, map_zero, hleft]
  simp

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

private theorem ordinaryTraceAlong_cutoffProjectionSandwich_eq_compression
    {ι κ μ H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (baseBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceBasis : HilbertBasis μ ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) baseBasis)
    (inclusion : K →L[ℂ] H) (cutoff : K →L[ℂ] K) :
    ordinaryTraceAlong targetBasis
        (data.right ∘L (inclusion ∘L cutoff ∘L inclusion†) ∘L
          data.left†) =
      ordinaryTraceAlong sourceBasis
        (inclusion† ∘L data.traceProduct ∘L inclusion ∘L cutoff) := by
  let projected := data.boundedPrecomp targetBasis sourceBasis inclusion
    (inclusion ∘L cutoff)
  have hcycle :=
    projected.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have hsource : projected.traceProduct =
      inclusion† ∘L data.traceProduct ∘L inclusion ∘L cutoff := by
    dsimp only [projected]
    rw [BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq]
  have htarget : projected.right ∘L projected.left† =
      data.right ∘L (inclusion ∘L cutoff ∘L inclusion†) ∘L
        data.left† := by
    dsimp only [projected, BasisHilbertSchmidtPairData.boundedPrecomp]
    rw [ContinuousLinearMap.adjoint_comp]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  calc
    ordinaryTraceAlong targetBasis
        (data.right ∘L (inclusion ∘L cutoff ∘L inclusion†) ∘L
          data.left†) =
        ordinaryTraceAlong targetBasis
          (projected.right ∘L projected.left†) :=
      congrArg (ordinaryTraceAlong targetBasis) htarget.symm
    _ = ordinaryTraceAlong sourceBasis projected.traceProduct := hcycle.symm
    _ = ordinaryTraceAlong sourceBasis
        (inclusion† ∘L data.traceProduct ∘L inclusion ∘L cutoff) :=
      congrArg (ordinaryTraceAlong sourceBasis) hsource

section BoundaryData

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {ι κ τ ιr κr τr ν μ σ : Type*}
variable (negativeBasis : HilbertBasis ι ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
variable (positiveBasis : HilbertBasis κ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
variable (outputBasis : HilbertBasis τ ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
variable (reflectedNegativeBasis : HilbertBasis ιr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
variable (reflectedPositiveBasis : HilbertBasis κr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
variable (reflectedOutputBasis : HilbertBasis τr ℂ
  (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
variable (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
variable (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
variable (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
variable (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
variable (N : ℕ)
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

/-- The common-boundary sandwich of the family-independent finite source
block. -/
noncomputable def sourceGatePhysicalPrefixBoundaryProjectionResponse :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L
    sourceGatePhysicalPrefixProjectionCoframe lambda sourceBasis N ∘L
      base.left†

/-- The common-boundary sandwich of the two centered finite-prefix physical
corners. -/
noncomputable def sourceGatePhysicalPrefixBoundaryCenteredResponse :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L
    sourceGatePhysicalPrefixCenteredCoframeDifference
      lambda family sourceBasis N ∘L base.left†

/-- Proof 738's finite boundary owner is the fixed prefix sandwich plus the
centered physical response. -/
theorem sourceGatePhysicalPrefixBoundaryCycleResponse_eq_projection_add_centered :
    sourceGatePhysicalPrefixBoundaryCycleResponse
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis N hfactor =
      sourceGatePhysicalPrefixBoundaryProjectionResponse
          owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis N hfactor +
        sourceGatePhysicalPrefixBoundaryCenteredResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change base.right ∘L
      sourceGatePhysicalPrefixCoframeDifference
        lambda family sourceBasis N ∘L base.left† =
    (base.right ∘L
      sourceGatePhysicalPrefixProjectionCoframe lambda sourceBasis N ∘L
        base.left†) +
      (base.right ∘L
        sourceGatePhysicalPrefixCenteredCoframeDifference
          lambda family sourceBasis N ∘L base.left†)
  rw [sourceGatePhysicalPrefixCoframeDifference_eq_projection_add_centered]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- The fixed finite-prefix boundary sandwich is trace legal. -/
theorem sourceGatePhysicalPrefixBoundaryProjectionResponse_isTraceClassAlong :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalPrefixBoundaryProjectionResponse
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis N hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L
      sourceGatePhysicalPrefixProjectionCoframe lambda sourceBasis N ∘L
        base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceGatePhysicalPrefixProjectionCoframe lambda sourceBasis N)

/-- The centered finite-prefix boundary sandwich is trace legal. -/
theorem sourceGatePhysicalPrefixBoundaryCenteredResponse_isTraceClassAlong :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalPrefixBoundaryCenteredResponse
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L
      sourceGatePhysicalPrefixCenteredCoframeDifference
        lambda family sourceBasis N ∘L base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceGatePhysicalPrefixCenteredCoframeDifference
      lambda family sourceBasis N)

/-- Every bounded source cutoff leaves the fixed block with zero boundary
trace; the result is specialized here to the literal prefix projection. -/
theorem ordinaryTraceAlong_prefixBoundaryProjectionResponse_eq_zero :
    ordinaryTraceAlong boundaryBasis
      (sourceGatePhysicalPrefixBoundaryProjectionResponse
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis N hfactor) = 0 := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let cutoff := basisPrefixProjection sourceBasis N
  have hcycle :=
    ordinaryTraceAlong_cutoffProjectionSandwich_eq_compression
      globalBasis boundaryBasis sourceBasis base (sourceInclusion lambda) cutoff
  have hbase : base.traceProduct =
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
    dsimp only [base]
    exact sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hcompressed :
      (sourceInclusion lambda)† ∘L base.traceProduct ∘L
          sourceInclusion lambda = 0 := by
    rw [hbase]
    exact sourceInclusionAdjoint_comp_threeBranch_comp_sourceInclusion_eq_zero
      owner lambda
  have hcompressedCutoff :
      (sourceInclusion lambda)† ∘L base.traceProduct ∘L
          sourceInclusion lambda ∘L cutoff = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator (cutoff x)) hcompressed
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hx ⊢
    exact hx
  rw [sourceGatePhysicalPrefixBoundaryProjectionResponse]
  change ordinaryTraceAlong boundaryBasis
      (base.right ∘L
        (sourceInclusion lambda ∘L cutoff ∘L
          (sourceInclusion lambda)†) ∘L base.left†) = 0
  rw [hcycle, hcompressedCutoff]
  simp only [ordinaryTraceAlong,
    ContinuousLinearMap.zero_apply, inner_zero_right, tsum_zero]

/-- The literal Gate prefix compression trace is exactly the centered
finite-prefix boundary trace; the fixed source block has disappeared. -/
theorem sourceGatePhysicalPrefixCompressionTrace_eq_centeredBoundaryCycle :
    CCM24FiniteSGatePhysicalPrefixCompression.sourceGatePhysicalPrefixCompressionTrace
        owner lambda family sourceBasis N =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCenteredResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  rw [sourceGatePhysicalPrefixCompressionTrace_eq_boundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis N hfactor]
  rw [sourceGatePhysicalPrefixBoundaryCycleResponse_eq_projection_add_centered
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis]
  rw [ordinaryTraceAlong_add boundaryBasis]
  · rw [ordinaryTraceAlong_prefixBoundaryProjectionResponse_eq_zero
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis N hfactor, zero_add]
  · exact sourceGatePhysicalPrefixBoundaryProjectionResponse_isTraceClassAlong
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis N hfactor
  · exact sourceGatePhysicalPrefixBoundaryCenteredResponse_isTraceClassAlong
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis N hfactor

/-- Proof 737's compact-root pairing is the same centered finite-prefix
boundary trace. -/
theorem sourceGatePhysicalPrefixRootPairing_eq_centeredBoundaryCycle :
    sourceGatePhysicalPrefixRootPairing owner lambda family sourceBasis N =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCenteredResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  rw [← sourceGatePhysicalPrefixCompressionTrace_eq_rootPairing]
  exact sourceGatePhysicalPrefixCompressionTrace_eq_centeredBoundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis N hfactor

include pairedBoundaryBasis

/-- A uniform bound on the centered finite-prefix boundary traces feeds the
ordered Gate consumer directly. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixCenteredBoundaryBound
    (bound : ℝ)
    (hbound : ∀ cutoffN : ℕ,
      ‖ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCenteredResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis cutoffN hfactor)‖ ≤
        bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply
    lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixRootPairingBound
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro cutoffN
  rw [sourceGatePhysicalPrefixRootPairing_eq_centeredBoundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis cutoffN hfactor]
  exact hbound cutoffN

end BoundaryData

end CCM24FiniteSGatePhysicalPrefixBoundaryCenteredCycle
end CCM25Concrete
end Source
end ConnesWeilRH
