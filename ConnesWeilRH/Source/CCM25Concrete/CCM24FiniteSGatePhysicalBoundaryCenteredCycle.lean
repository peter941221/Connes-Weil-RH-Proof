/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalBoundaryCycle

/-!
# Centered physical boundary cycle for the Gate response

Proof 730 cycles the Gate response to the common physical boundary with middle
operator

```text
C_S = D_S J^dagger - J F_S^dagger.
```

Writing `U_S = D_S - J` and `R = J J^dagger` gives the exact decomposition

```text
C_S = R + C_S^0,
C_S^0 = U_S J^dagger - J F_S^dagger.
```

The centered operator has zero `R/R` and `(I-R)/(I-R)` corners.  Moreover the
genuine three-branch owner is `[R,W]`, so `J^dagger [R,W] J = 0`.  A legal
Hilbert--Schmidt cycle therefore removes the fixed `R` sandwich from the
boundary trace exactly.

No uniform estimate, finite-S sign, Burnol identity, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalBoundaryCenteredCycle

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalBoundaryCycle
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The centered ambient coframe -/

/-- The family-dependent part of the cycled coframe after removing the fixed
source-Sonin projection.  Its two terms are the opposite off-diagonal corners. -/
noncomputable def sourceGatePhysicalCenteredCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceEndpointCancellationResidual lambda family ∘L
      (sourceInclusion lambda)† -
    sourceInclusion lambda ∘L
      (sourceActualBandForwardCoframe lambda family)†

/-- Proof 730's middle operator is the fixed source projection plus its
centered off-diagonal part. -/
theorem sourceGatePhysicalCoframeDifference_eq_projection_add_centered
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGatePhysicalCoframeDifference lambda family =
      sourceSoninProjection lambda +
        sourceGatePhysicalCenteredCoframeDifference lambda family := by
  rw [sourceGatePhysicalCoframeDifference,
    sourceGatePhysicalCenteredCoframeDifference,
    sourceEndpointCancellationResidual_eq_endpoint_sub_inclusion,
    ← sourceInclusion_comp_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply]
  abel

/-- The adjoint forward coframe annihilates the source inclusion. -/
theorem sourceActualBandForwardCoframe_adjoint_comp_sourceInclusion_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceActualBandForwardCoframe lambda family)† ∘L
        sourceInclusion lambda = 0 := by
  have hcross :=
    sourceInclusionAdjoint_comp_sourceActualBandForwardCoframe_eq_zero
      lambda family
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hz := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator y) hcross
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hz
  rw [hz]
  simp

/-- The left source-Sonin compression of the centered coframe is exactly the
reverse-forward corner. -/
theorem sourceSoninProjection_comp_sourceGatePhysicalCenteredCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceGatePhysicalCenteredCoframeDifference lambda family =
      -(sourceInclusion lambda ∘L
        (sourceActualBandForwardCoframe lambda family)†) := by
  apply ContinuousLinearMap.ext
  intro x
  have hresidual := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (((sourceInclusion lambda)†) x))
    (sourceSoninProjection_comp_sourceEndpointCancellationResidual_eq_zero
      lambda family)
  have hinclusion := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (((sourceActualBandForwardCoframe lambda family)†) x))
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [sourceGatePhysicalCenteredCoframeDifference,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply,
    map_sub] at hresidual hinclusion ⊢
  rw [hresidual, hinclusion]
  simp

/-- The right source-Sonin compression of the centered coframe is exactly the
endpoint-residual corner. -/
theorem sourceGatePhysicalCenteredCoframeDifference_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceGatePhysicalCenteredCoframeDifference lambda family ∘L
        sourceSoninProjection lambda =
      sourceEndpointCancellationResidual lambda family ∘L
        (sourceInclusion lambda)† := by
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
  simp only [sourceGatePhysicalCenteredCoframeDifference,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] at hinclusion hforward ⊢
  rw [hinclusion, hforward]
  simp

/-- The centered coframe has no source-Sonin diagonal corner. -/
theorem sourceGatePhysicalCenteredCoframeDifference_sourceSonin_corner_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceGatePhysicalCenteredCoframeDifference lambda family ∘L
        sourceSoninProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hright := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
    (sourceGatePhysicalCenteredCoframeDifference_comp_sourceSoninProjection
      lambda family)
  have hleft := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (((sourceInclusion lambda)†) x))
    (sourceSoninProjection_comp_sourceEndpointCancellationResidual_eq_zero
      lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hright hleft ⊢
  rw [hright, hleft]

/-- The centered coframe also has no complementary diagonal corner. -/
theorem sourceGatePhysicalCenteredCoframeDifference_complement_corner_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda) ∘L
        sourceGatePhysicalCenteredCoframeDifference lambda family ∘L
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
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hright
  have hcentered :
      sourceGatePhysicalCenteredCoframeDifference lambda family
          (complement x) =
        -(sourceInclusion lambda
          (((sourceActualBandForwardCoframe lambda family)†)
            (complement x))) := by
    simp only [sourceGatePhysicalCenteredCoframeDifference,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [hright]
    simp
  have hleft := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator
        (((sourceActualBandForwardCoframe lambda family)†) (complement x)))
    hcomplementInclusion
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hleft
  change complement
      (sourceGatePhysicalCenteredCoframeDifference lambda family
        (complement x)) = 0
  rw [hcentered, map_neg, hleft]
  simp

/-! ## The fixed projection block has zero compressed commutator -/

/-- Compressing the genuine three-branch commutator to the source Sonin
carrier gives zero exactly. -/
theorem sourceInclusionAdjoint_comp_threeBranch_comp_sourceInclusion_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        sourceInclusion lambda = 0 := by
  rw [← sourceSoninCommutator_eq_threeBranch]
  unfold cc20Commutator
  apply ContinuousLinearMap.ext
  intro x
  have hleft := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda x)))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  have hright := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    map_sub] at hleft hright ⊢
  rw [hleft, hright, sub_self]

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

private theorem ordinaryTraceAlong_projectionSandwich_eq_compression
    {ι κ μ H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (baseBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceBasis : HilbertBasis μ ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) baseBasis)
    (inclusion : K →L[ℂ] H) :
    ordinaryTraceAlong targetBasis
        (data.right ∘L (inclusion ∘L inclusion†) ∘L data.left†) =
      ordinaryTraceAlong sourceBasis
        (inclusion† ∘L data.traceProduct ∘L inclusion) := by
  let projected :=
    data.boundedPrecomp targetBasis sourceBasis inclusion inclusion
  have hcycle :=
    projected.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
  have hsource : projected.traceProduct =
      inclusion† ∘L data.traceProduct ∘L inclusion := by
    dsimp only [projected]
    exact BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq
      targetBasis sourceBasis data inclusion inclusion
  have htarget : projected.right ∘L projected.left† =
      data.right ∘L (inclusion ∘L inclusion†) ∘L data.left† := by
    dsimp only [projected, BasisHilbertSchmidtPairData.boundedPrecomp]
    rw [ContinuousLinearMap.adjoint_comp]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  calc
    ordinaryTraceAlong targetBasis
        (data.right ∘L (inclusion ∘L inclusion†) ∘L data.left†) =
        ordinaryTraceAlong targetBasis
          (projected.right ∘L projected.left†) :=
      congrArg (ordinaryTraceAlong targetBasis) htarget.symm
    _ = ordinaryTraceAlong sourceBasis projected.traceProduct := hcycle.symm
    _ = ordinaryTraceAlong sourceBasis
        (inclusion† ∘L data.traceProduct ∘L inclusion) :=
      congrArg (ordinaryTraceAlong sourceBasis) hsource

/-! ## The centered boundary owner -/

section BoundaryData

variable (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
variable (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
variable (a c : ℝ) (hac : a ≤ c)
variable (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
variable {ι κ τ ιr κr τr ν μ ρ : Type*}
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
variable (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
variable (hfactor : Summable fun i =>
  ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)

/-- The boundary sandwich of the fixed source-Sonin projection. -/
noncomputable def sourceGatePhysicalBoundaryProjectionResponse :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L sourceSoninProjection lambda ∘L base.left†

/-- The boundary sandwich of the two off-diagonal coframe corners. -/
noncomputable def sourceGatePhysicalBoundaryCenteredResponse :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L
    sourceGatePhysicalCenteredCoframeDifference lambda family ∘L base.left†

/-- The Proof 730 boundary operator is its fixed projection sandwich plus the
centered boundary response. -/
theorem sourceGatePhysicalBoundaryCycleResponse_eq_projection_add_centered :
    sourceGatePhysicalBoundaryCycleResponse
        (ι := ι) (κ := κ) (τ := τ) (ιr := ιr) (κr := κr) (τr := τr)
        (ν := ν) owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor =
      sourceGatePhysicalBoundaryProjectionResponse owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor +
        sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change base.right ∘L sourceGatePhysicalCoframeDifference lambda family ∘L
      base.left† =
    (base.right ∘L sourceSoninProjection lambda ∘L base.left†) +
      (base.right ∘L
        sourceGatePhysicalCenteredCoframeDifference lambda family ∘L
        base.left†)
  rw [sourceGatePhysicalCoframeDifference_eq_projection_add_centered]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- The fixed projection sandwich is trace legal on the common boundary. -/
theorem sourceGatePhysicalBoundaryProjectionResponse_isTraceClassAlong :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalBoundaryProjectionResponse owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L sourceSoninProjection lambda ∘L base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceSoninProjection lambda)

/-- The centered boundary response is trace legal on the common boundary. -/
theorem sourceGatePhysicalBoundaryCenteredResponse_isTraceClassAlong :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L
      sourceGatePhysicalCenteredCoframeDifference lambda family ∘L base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceGatePhysicalCenteredCoframeDifference lambda family)

include sourceBasis

/-- The fixed source-projection sandwich has exactly zero boundary trace. -/
theorem ordinaryTraceAlong_sourceGatePhysicalBoundaryProjectionResponse_eq_zero :
    ordinaryTraceAlong boundaryBasis
      (sourceGatePhysicalBoundaryProjectionResponse owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) = 0 := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hcycle := ordinaryTraceAlong_projectionSandwich_eq_compression
    globalBasis boundaryBasis sourceBasis base (sourceInclusion lambda)
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
  rw [sourceGatePhysicalBoundaryProjectionResponse]
  change ordinaryTraceAlong boundaryBasis
      (base.right ∘L sourceSoninProjection lambda ∘L base.left†) = 0
  rw [← sourceInclusion_comp_adjoint] at ⊢
  rw [hcycle, hcompressed]
  simp only [ordinaryTraceAlong, ContinuousLinearMap.zero_apply,
    inner_zero_right, tsum_zero]

/-- The Gate trace is exactly the trace of the centered off-diagonal boundary
response; the fixed `R` block has disappeared. -/
theorem ordinaryTraceAlong_lowerFactorGaugedResponse_eq_centeredBoundaryCycle :
    ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family) =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor) := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_boundaryCycle owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [sourceGatePhysicalBoundaryCycleResponse_eq_projection_add_centered owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_add boundaryBasis]
  · rw [ordinaryTraceAlong_sourceGatePhysicalBoundaryProjectionResponse_eq_zero
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor (sourceBasis := sourceBasis),
      zero_add]
  · exact sourceGatePhysicalBoundaryProjectionResponse_isTraceClassAlong owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor
  · exact sourceGatePhysicalBoundaryCenteredResponse_isTraceClassAlong owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor

/-- Every scalar Gate trace-norm bound is equivalent to the same bound for the
centered boundary response. -/
theorem lowerFactorGaugedResponse_trace_norm_le_iff_centeredBoundaryCycle
    (bound : ℝ) :
    ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound ↔
      ‖ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalBoundaryCenteredResponse owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor)‖ ≤
        bound := by
  rw [ordinaryTraceAlong_lowerFactorGaugedResponse_eq_centeredBoundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]

end BoundaryData

end CCM24FiniteSGatePhysicalBoundaryCenteredCycle
end CCM25Concrete
end Source
end ConnesWeilRH
