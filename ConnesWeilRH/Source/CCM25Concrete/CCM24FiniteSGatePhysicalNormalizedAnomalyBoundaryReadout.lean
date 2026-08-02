/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalNormalizedAnomalyTrace

/-!
# Physical boundary readout of the normalized Gram anomaly

Proof 749 shows that the normalized Gram-order anomaly has a legal, generally
pure-imaginary ordinary trace.  This module identifies that trace with the
actual bidirectional physical coframe boundary on the ambient finite-S
carrier.

Write `J` for the source inclusion, `R = J J†`, `Hhat` for the normalized
ambient Gram, `Ahat` for the normalized inverse source Gram, and `L` for the
completed physical coframe leakage.  The lifted inverse Gram

`Phat = J Ahat J†`

satisfies the exact source-specific identity

`Phat [R,Hhat] - [R,Hhat] Phat = J L† + L J†`.

The completed four-branch Hilbert--Schmidt pair then licenses the rectangular
cycle from the source anomaly to

`(1 / 2) Tr_ambient([W,R] (J L† + L J†))`.

This is an identity for one signed physical object.  It is not a separate
uniform estimate of either leakage orientation, and it does not make the
anomaly vanish.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalNormalizedAnomalyTrace
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
open CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace
open CC20Concrete.CompactRootHalfLinePair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem adjoint_sub_endomorphism
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (left right : H →L[ℂ] H) :
    (left - right)† = left† - right† := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

private theorem boundary_vector_identity_of_eq
    {H : Type*} [AddCommGroup H]
    (sumValue rangeValue baseValue leftValue rightValue : H)
    (hsum : sumValue = baseValue + leftValue)
    (hrange : rangeValue = baseValue) :
    (sumValue - rangeValue) -
        (rangeValue - (baseValue + rightValue)) =
      leftValue + rightValue := by
  rw [hsum, hrange]
  abel

/-- The lower-factor-normalized ambient Gram remains self-adjoint. -/
theorem finiteEulerLowerFactorNormalizedAmbientGram_isSelfAdjoint
    (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerLowerFactorNormalizedAmbientGram family) := by
  rw [finiteEulerLowerFactorNormalizedAmbientGram]
  apply IsSelfAdjoint.smul
  · change IsSelfAdjoint
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹)
    simp [IsSelfAdjoint]
  · exact finiteEulerAmbientGram_isSelfAdjoint family

/-- The normalized inverse source Gram remains self-adjoint. -/
theorem finiteEulerNormalizedSourceGramInv_isSelfAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerNormalizedSourceGramInv lambda family) := by
  rw [finiteEulerNormalizedSourceGramInv]
  apply IsSelfAdjoint.smul
  · change IsSelfAdjoint
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)
    simp [IsSelfAdjoint]
  · exact finiteEulerGramInv_isSelfAdjoint lambda family

/-- The fixed detector boundary `[W,R]` is skew-adjoint. -/
theorem sourceBoundaryCommutator_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (sourceBoundaryCommutator owner lambda)† =
      -sourceBoundaryCommutator owner lambda := by
  rw [sourceBoundaryCommutator, adjoint_sub_endomorphism,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  abel

/-- The normalized metric boundary `[R,Hhat]` is skew-adjoint. -/
theorem finiteEulerNormalizedMetricBoundaryCommutator_adjoint_eq_neg
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerNormalizedMetricBoundaryCommutator lambda family)† =
      -finiteEulerNormalizedMetricBoundaryCommutator lambda family := by
  rw [finiteEulerNormalizedMetricBoundaryCommutator,
    adjoint_sub_endomorphism, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (finiteEulerLowerFactorNormalizedAmbientGram_isSelfAdjoint
      family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  abel

/-- The normalized right numerator is the reverse ordering of the two actual
ambient boundary commutators. -/
theorem finiteEulerNormalizedRightBoundaryNumerator_eq_reverseDoubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedRightBoundaryNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L
        sourceBoundaryCommutator owner lambda ∘L
          finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
            sourceInclusion lambda := by
  rw [← finiteEulerNormalizedLeftBoundaryNumerator_adjoint_eq_right,
    finiteEulerNormalizedLeftBoundaryNumerator_eq_doubleBoundary]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    sourceBoundaryCommutator_adjoint_eq_neg,
    finiteEulerNormalizedMetricBoundaryCommutator_adjoint_eq_neg]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg, neg_neg]

/-- The source anomaly is the inverse Gram applied to the commutator of the
two actual normalized ambient boundaries. -/
theorem finiteEulerNormalizedGramSimilarityAnomaly_eq_doubleBoundaryCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedGramSimilarityAnomaly owner lambda family =
      (1 / 2 : ℂ) •
        (finiteEulerNormalizedSourceGramInv lambda family ∘L
              (sourceInclusion lambda)† ∘L
              finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
              sourceBoundaryCommutator owner lambda ∘L
              sourceInclusion lambda -
          finiteEulerNormalizedSourceGramInv lambda family ∘L
              (sourceInclusion lambda)† ∘L
              sourceBoundaryCommutator owner lambda ∘L
              finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
              sourceInclusion lambda) := by
  rw [finiteEulerNormalizedGramSimilarityAnomaly_eq_boundaryDifference,
    finiteEulerNormalizedLeftBoundaryNumerator_eq_doubleBoundary,
    finiteEulerNormalizedRightBoundaryNumerator_eq_reverseDoubleBoundary]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub]

/-- Ambient lift `J Ahat J†` of the normalized inverse source Gram.  It is
not called a projection: only its source-range support is used below. -/
noncomputable def finiteEulerNormalizedInverseGramLift
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceInclusion lambda ∘L
    finiteEulerNormalizedSourceGramInv lambda family ∘L
      (sourceInclusion lambda)†

theorem finiteEulerNormalizedInverseGramLift_isSelfAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerNormalizedInverseGramLift lambda family) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [finiteEulerNormalizedInverseGramLift,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (finiteEulerNormalizedSourceGramInv_isSelfAdjoint
      lambda family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The scalar gauges in `Hhat J Ahat` cancel exactly, leaving the original
inverse-metric coframe. -/
theorem normalizedAmbientGram_comp_inclusion_comp_sourceGramInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerLowerFactorNormalizedAmbientGram family ∘L
        sourceInclusion lambda ∘L
          finiteEulerNormalizedSourceGramInv lambda family =
      finiteEulerMetricCoframe lambda family := by
  have hc : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerLowerFactorNormalizedAmbientGram,
    finiteEulerNormalizedSourceGramInv, finiteEulerMetricCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hc), one_smul]

/-- The complete physical coframe is the source inclusion plus its completed
outer/second-support/prolate leakage. -/
theorem finiteEulerMetricCoframe_eq_inclusion_add_physicalLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      sourceInclusion lambda + sourcePhysicalCoframeLeakage lambda family := by
  rw [← sourceSoninCoframeLeakage_eq_physical,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]
  abel

/-- The two physical source/complement orientations kept as one ambient
boundary operator. -/
noncomputable def sourceBidirectionalPhysicalCoframeBoundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceInclusion lambda ∘L (sourcePhysicalCoframeLeakage lambda family)† +
    sourcePhysicalCoframeLeakage lambda family ∘L
      (sourceInclusion lambda)†

/-- The normalized Gram-order obstruction is exactly the bidirectional
physical coframe boundary. -/
theorem normalizedInverseGramLift_metricBoundary_commutator_eq_physical
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedInverseGramLift lambda family ∘L
          finiteEulerNormalizedMetricBoundaryCommutator lambda family -
        finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
          finiteEulerNormalizedInverseGramLift lambda family =
      sourceBidirectionalPhysicalCoframeBoundary lambda family := by
  let J := sourceInclusion lambda
  let R := sourceSoninProjection lambda
  let H := finiteEulerLowerFactorNormalizedAmbientGram family
  let A := finiteEulerNormalizedSourceGramInv lambda family
  let P := finiteEulerNormalizedInverseGramLift lambda family
  let C := finiteEulerMetricCoframe lambda family
  let L := sourcePhysicalCoframeLeakage lambda family
  have hJR : J† ∘L J = ContinuousLinearMap.id ℂ
      (sourceSoninCarrier lambda) := sourceInclusion_adjoint_comp_self lambda
  have hR : J ∘L J† = R := by
    exact sourceInclusion_comp_adjoint lambda
  have hPR : P ∘L R = P := by
    apply ContinuousLinearMap.ext
    intro u
    have hpoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator ((J†) u)) hJR
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hpoint
    simp only [P, R, finiteEulerNormalizedInverseGramLift,
      ContinuousLinearMap.comp_apply]
    rw [← sourceInclusion_comp_adjoint lambda]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hpoint]
  have hRP : R ∘L P = P := by
    apply ContinuousLinearMap.ext
    intro u
    have hpoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator (A ((J†) u))) hJR
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hpoint
    simp only [P, R, finiteEulerNormalizedInverseGramLift,
      ContinuousLinearMap.comp_apply]
    rw [← sourceInclusion_comp_adjoint lambda]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hpoint]
  have hHP : H ∘L P = C ∘L J† := by
    apply ContinuousLinearMap.ext
    intro u
    have hpoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator ((J†) u))
      (normalizedAmbientGram_comp_inclusion_comp_sourceGramInv lambda family)
    simpa only [H, P, C, finiteEulerNormalizedInverseGramLift,
      ContinuousLinearMap.comp_apply] using hpoint
  have hPH : P ∘L H = J ∘L C† := by
    have h := congrArg ContinuousLinearMap.adjoint hHP
    have hPAdjoint : P† = P := by
      simpa only [P] using
        (finiteEulerNormalizedInverseGramLift_isSelfAdjoint
          lambda family).adjoint_eq
    have hHAdjoint : H† = H := by
      simpa only [H] using
        (finiteEulerLowerFactorNormalizedAmbientGram_isSelfAdjoint
          family).adjoint_eq
    simpa only [ContinuousLinearMap.adjoint_comp, hPAdjoint, hHAdjoint,
      ContinuousLinearMap.adjoint_adjoint] using h
  have hPHR : P ∘L H ∘L R = R := by
    apply ContinuousLinearMap.ext
    intro u
    have hmetric := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator ((J†) u))
      (metricCoframeAdjoint_comp_sourceInclusion lambda family)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hmetric
    simp only [ContinuousLinearMap.comp_apply]
    rw [show P (H (R u)) = J ((C†) (R u)) by
      exact congrFun (congrArg DFunLike.coe hPH) (R u)]
    have hRPoint := congrFun (congrArg DFunLike.coe hR) u
    simp only [ContinuousLinearMap.comp_apply] at hRPoint
    rw [← hRPoint]
    rw [hmetric]
  have hRHP : R ∘L H ∘L P = R := by
    apply ContinuousLinearMap.ext
    intro u
    have hmetric := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator ((J†) u))
      (sourceSoninProjection_comp_metricCoframe lambda family)
    simp only [ContinuousLinearMap.comp_apply] at hmetric
    simp only [ContinuousLinearMap.comp_apply]
    rw [show H (P u) = C ((J†) u) by
      exact congrFun (congrArg DFunLike.coe hHP) u]
    rw [hmetric]
    exact congrFun (congrArg DFunLike.coe hR) u
  have hC : C = J + L := by
    exact finiteEulerMetricCoframe_eq_inclusion_add_physicalLeakage
      lambda family
  have hCadj : C† = J† + L† := by
    have h := congrArg ContinuousLinearMap.adjoint hC
    simpa only [ContinuousLinearMap.adjoint.map_add,
      ContinuousLinearMap.adjoint_adjoint] using h
  rw [finiteEulerNormalizedMetricBoundaryCommutator]
  change P ∘L (R ∘L H - H ∘L R) -
      (R ∘L H - H ∘L R) ∘L P = _
  apply ContinuousLinearMap.ext
  intro u
  have hPRPoint := congrFun (congrArg DFunLike.coe hPR) (H u)
  have hRPPoint := congrFun (congrArg DFunLike.coe hRP) u
  have hPHRPoint := congrFun (congrArg DFunLike.coe hPHR) u
  have hRHPPoint := congrFun (congrArg DFunLike.coe hRHP) u
  have hPHPoint := congrFun (congrArg DFunLike.coe hPH) u
  have hHPPoint := congrFun (congrArg DFunLike.coe hHP) u
  have hCPoint := congrFun (congrArg DFunLike.coe hC) ((J†) u)
  have hCadjPoint := congrFun (congrArg DFunLike.coe hCadj) u
  have hRPoint := congrFun (congrArg DFunLike.coe hR) u
  have hJadd : J ((J†) u + (L†) u) =
      J ((J†) u) + J ((L†) u) := map_add J _ _
  simp only [ContinuousLinearMap.comp_apply] at hPRPoint hRPPoint hPHRPoint
  simp only [ContinuousLinearMap.comp_apply] at hRHPPoint hPHPoint hHPPoint
  simp only [ContinuousLinearMap.comp_apply] at hRPoint
  simp only [ContinuousLinearMap.add_apply] at hCPoint hCadjPoint
  simp only [sourceBidirectionalPhysicalCoframeBoundary,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_sub]
  change (P (R (H u)) - P (H (R u))) -
      (R (H (P u)) - H (R (P u))) =
    J ((L†) u) + L ((J†) u)
  calc
    (P (R (H u)) - P (H (R u))) -
          (R (H (P u)) - H (R (P u))) =
        (P (H u) - R u) - (R u - H (P u)) := by
      rw [hPRPoint, hPHRPoint, hRHPPoint, hRPPoint]
    _ = (J ((C†) u) - R u) -
        (R u - C ((J†) u)) := by
      exact congrArg₂ (fun left right =>
        (left - R u) - (R u - right)) hPHPoint hHPPoint
    _ = (J ((J†) u + (L†) u) - R u) -
        (R u - (J ((J†) u) + L ((J†) u))) := by
      exact congrArg₂ (fun left right =>
        (J left - R u) - (R u - right)) hCadjPoint hCPoint
    _ = J ((L†) u) + L ((J†) u) := by
      exact boundary_vector_identity_of_eq
        (J ((J†) u + (L†) u)) (R u) (J ((J†) u))
        (J ((L†) u)) (L ((J†) u)) hJadd hRPoint.symm

/-- Ambient trace owner of the normalized anomaly after both physical
coframe orientations have been recombined. -/
noncomputable def finiteEulerNormalizedPhysicalAnomalyBoundaryReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (1 / 2 : ℂ) •
    (sourceBoundaryCommutator owner lambda ∘L
      sourceBidirectionalPhysicalCoframeBoundary lambda family)

private noncomputable def rectangularSandwichPairData
    {H K G iota kappa rho : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (ambientBasis : HilbertBasis iota ℂ H)
    (factorBasis : HilbertBasis kappa ℂ G)
    (sourceBasis : HilbertBasis rho ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) ambientBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    BasisHilbertSchmidtPairData (G := G) sourceBasis where
  left := data.left ∘L leftBounded
  right := data.right ∘L rightBounded
  left_summable_normSq :=
    CC20Concrete.PositiveTrace.summable_normSq_precomp ambientBasis factorBasis
      sourceBasis data.left leftBounded data.left_summable_normSq
  right_summable_normSq :=
    CC20Concrete.PositiveTrace.summable_normSq_precomp ambientBasis factorBasis
      sourceBasis data.right rightBounded data.right_summable_normSq

private theorem rectangularSandwichPairData_traceProduct_eq
    {H K G iota kappa rho : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (ambientBasis : HilbertBasis iota ℂ H)
    (factorBasis : HilbertBasis kappa ℂ G)
    (sourceBasis : HilbertBasis rho ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) ambientBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    (rectangularSandwichPairData ambientBasis factorBasis sourceBasis data
      leftBounded rightBounded).traceProduct =
        leftBounded† ∘L data.traceProduct ∘L rightBounded := by
  unfold rectangularSandwichPairData
  rw [BasisHilbertSchmidtPairData.traceProduct,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

private theorem rectangularSandwich_isTraceClassAlong
    {H K G iota kappa rho : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (ambientBasis : HilbertBasis iota ℂ H)
    (factorBasis : HilbertBasis kappa ℂ G)
    (sourceBasis : HilbertBasis rho ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) ambientBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    IsTraceClassAlong sourceBasis
      (leftBounded† ∘L data.traceProduct ∘L rightBounded) := by
  rw [← rectangularSandwichPairData_traceProduct_eq ambientBasis factorBasis
    sourceBasis data leftBounded rightBounded]
  exact (rectangularSandwichPairData ambientBasis factorBasis sourceBasis data
    leftBounded rightBounded).traceProduct_isTraceClassAlong

private theorem ordinaryTraceAlong_rectangularSandwich_eq_cycle
    {H K G iota kappa rho : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (ambientBasis : HilbertBasis iota ℂ H)
    (factorBasis : HilbertBasis kappa ℂ G)
    (sourceBasis : HilbertBasis rho ℂ K)
    (data : BasisHilbertSchmidtPairData (G := G) ambientBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    ordinaryTraceAlong sourceBasis
        (leftBounded† ∘L data.traceProduct ∘L rightBounded) =
      ordinaryTraceAlong ambientBasis
        (data.traceProduct ∘L rightBounded ∘L leftBounded†) := by
  let sourcePair := rectangularSandwichPairData ambientBasis factorBasis
    sourceBasis data leftBounded rightBounded
  let ambientPair := data.boundedSandwich factorBasis
    (ContinuousLinearMap.id ℂ H) (rightBounded ∘L leftBounded†)
  have hsource : sourcePair.traceProduct =
      leftBounded† ∘L data.traceProduct ∘L rightBounded := by
    exact rectangularSandwichPairData_traceProduct_eq ambientBasis factorBasis
      sourceBasis data leftBounded rightBounded
  have hambient : ambientPair.traceProduct =
      data.traceProduct ∘L rightBounded ∘L leftBounded† := by
    dsimp only [ambientPair]
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have htarget :
      sourcePair.right ∘L sourcePair.left† =
        ambientPair.right ∘L ambientPair.left† := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [sourcePair, ambientPair, rectangularSandwichPairData,
      BasisHilbertSchmidtPairData.boundedSandwich,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  calc
    ordinaryTraceAlong sourceBasis
        (leftBounded† ∘L data.traceProduct ∘L rightBounded) =
        ordinaryTraceAlong sourceBasis sourcePair.traceProduct := by
      rw [hsource]
    _ = ordinaryTraceAlong factorBasis
        (sourcePair.right ∘L sourcePair.left†) :=
      sourcePair.ordinaryTraceAlong_traceProduct_eq_cyclic factorBasis
    _ = ordinaryTraceAlong factorBasis
        (ambientPair.right ∘L ambientPair.left†) := by rw [htarget]
    _ = ordinaryTraceAlong ambientBasis ambientPair.traceProduct :=
      (ambientPair.ordinaryTraceAlong_traceProduct_eq_cyclic
        factorBasis).symm
    _ = ordinaryTraceAlong ambientBasis
        (data.traceProduct ∘L rightBounded ∘L leftBounded†) := by rw [hambient]

/-- The ambient physical anomaly readout is trace legal for each fixed finite
family.  This is not a family-uniform trace-norm estimate. -/
theorem finiteEulerNormalizedPhysicalAnomalyBoundaryReadout_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      (finiteEulerNormalizedPhysicalAnomalyBoundaryReadout
        owner lambda family) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let data := base.smulRight (-1)
  let D := sourceBoundaryCommutator owner lambda
  let M := finiteEulerNormalizedMetricBoundaryCommutator lambda family
  let P := finiteEulerNormalizedInverseGramLift lambda family
  have hdata : data.traceProduct = D := by
    dsimp only [data, base, D]
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      sourceThreeBranchPairData_traceProduct_eq,
      sourceBoundaryCommutator_eq_neg_threeBranch]
    simp only [neg_one_smul]
  have hfirst : IsTraceClassAlong globalBasis (D ∘L P ∘L M) := by
    have hclass := data.boundedSandwich_isTraceClassAlong boundaryBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier) (P ∘L M)
    rw [hdata] at hclass
    simpa only [ContinuousLinearMap.id_comp] using hclass
  have hsecond : IsTraceClassAlong globalBasis (D ∘L M ∘L P) := by
    have hclass := data.boundedSandwich_isTraceClassAlong boundaryBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier) (M ∘L P)
    rw [hdata] at hclass
    simpa only [ContinuousLinearMap.id_comp] using hclass
  rw [finiteEulerNormalizedPhysicalAnomalyBoundaryReadout,
    ← normalizedInverseGramLift_metricBoundary_commutator_eq_physical]
  have hop : D ∘L (P ∘L M - M ∘L P) =
      D ∘L P ∘L M - D ∘L M ∘L P := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, map_sub]
  rw [hop]
  exact isTraceClassAlong_smul globalBasis _ _
    (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      globalBasis _ _ hfirst hsecond)

/-- The source anomaly trace is exactly the ambient detector pairing with the
two-sided physical coframe leakage. -/
theorem ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_physicalBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedGramSimilarityAnomaly owner lambda family) =
      ordinaryTraceAlong globalBasis
        (finiteEulerNormalizedPhysicalAnomalyBoundaryReadout
          owner lambda family) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let data := base.smulRight (-1)
  let D := sourceBoundaryCommutator owner lambda
  let M := finiteEulerNormalizedMetricBoundaryCommutator lambda family
  let A := finiteEulerNormalizedSourceGramInv lambda family
  let J := sourceInclusion lambda
  let P := finiteEulerNormalizedInverseGramLift lambda family
  let firstLeft := M† ∘L J ∘L A†
  let secondLeft := J ∘L A†
  let firstSource := A ∘L J† ∘L M ∘L D ∘L J
  let secondSource := A ∘L J† ∘L D ∘L M ∘L J
  let firstAmbient := D ∘L P ∘L M
  let secondAmbient := D ∘L M ∘L P
  have hdata : data.traceProduct = D := by
    dsimp only [data, base, D]
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      sourceThreeBranchPairData_traceProduct_eq,
      sourceBoundaryCommutator_eq_neg_threeBranch]
    simp only [neg_one_smul]
  have hfirstSourceOp : firstLeft† ∘L D ∘L J = firstSource := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [firstLeft, firstSource, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply]
  have hsecondSourceOp : secondLeft† ∘L D ∘L (M ∘L J) =
      secondSource := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [secondLeft, secondSource, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply]
  have hfirstAmbientOp : D ∘L J ∘L firstLeft† = firstAmbient := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [firstLeft, firstAmbient, P, A, J, M, D,
      finiteEulerNormalizedInverseGramLift,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply]
  have hsecondAmbientOp : D ∘L (M ∘L J) ∘L secondLeft† =
      secondAmbient := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [secondLeft, secondAmbient, P, A, J, M, D,
      finiteEulerNormalizedInverseGramLift,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply]
  have hfirstCycle : ordinaryTraceAlong sourceBasis firstSource =
      ordinaryTraceAlong globalBasis firstAmbient := by
    have hcycle := ordinaryTraceAlong_rectangularSandwich_eq_cycle globalBasis
      boundaryBasis sourceBasis data firstLeft J
    rw [hdata, hfirstSourceOp, hfirstAmbientOp] at hcycle
    exact hcycle
  have hsecondCycle : ordinaryTraceAlong sourceBasis secondSource =
      ordinaryTraceAlong globalBasis secondAmbient := by
    have hcycle := ordinaryTraceAlong_rectangularSandwich_eq_cycle globalBasis
      boundaryBasis sourceBasis data secondLeft (M ∘L J)
    rw [hdata, hsecondSourceOp, hsecondAmbientOp] at hcycle
    exact hcycle
  have hfirstSource : IsTraceClassAlong sourceBasis firstSource := by
    have hclass := rectangularSandwich_isTraceClassAlong globalBasis
      boundaryBasis sourceBasis data firstLeft J
    rw [hdata, hfirstSourceOp] at hclass
    exact hclass
  have hsecondSource : IsTraceClassAlong sourceBasis secondSource := by
    have hclass := rectangularSandwich_isTraceClassAlong globalBasis
      boundaryBasis sourceBasis data secondLeft (M ∘L J)
    rw [hdata, hsecondSourceOp] at hclass
    exact hclass
  have hfirstAmbient : IsTraceClassAlong globalBasis firstAmbient := by
    have hclass := data.boundedSandwich_isTraceClassAlong boundaryBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier) (P ∘L M)
    rw [hdata] at hclass
    simpa only [firstAmbient, ContinuousLinearMap.id_comp] using hclass
  have hsecondAmbient : IsTraceClassAlong globalBasis secondAmbient := by
    have hclass := data.boundedSandwich_isTraceClassAlong boundaryBasis
      (ContinuousLinearMap.id ℂ finiteSCarrier) (M ∘L P)
    rw [hdata] at hclass
    simpa only [secondAmbient, ContinuousLinearMap.id_comp] using hclass
  have hsourceOperator :
      finiteEulerNormalizedGramSimilarityAnomaly owner lambda family =
        (1 / 2 : ℂ) • (firstSource - secondSource) := by
    simpa only [firstSource, secondSource, A, J, M, D] using
      (finiteEulerNormalizedGramSimilarityAnomaly_eq_doubleBoundaryCommutator
        owner lambda family)
  have hambientOperator :
      finiteEulerNormalizedPhysicalAnomalyBoundaryReadout owner lambda family =
        (1 / 2 : ℂ) • (firstAmbient - secondAmbient) := by
    rw [finiteEulerNormalizedPhysicalAnomalyBoundaryReadout,
      ← normalizedInverseGramLift_metricBoundary_commutator_eq_physical]
    apply ContinuousLinearMap.ext
    intro u
    simp only [firstAmbient, secondAmbient, P, M, D,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, map_sub]
  rw [hsourceOperator, hambientOperator]
  rw [ordinaryTraceAlong_smul sourceBasis _ _
    (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      sourceBasis _ _ hfirstSource hsecondSource)]
  rw [ordinaryTraceAlong_smul globalBasis _ _
    (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      globalBasis _ _ hfirstAmbient hsecondAmbient)]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
    sourceBasis _ _ hfirstSource hsecondSource]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
    globalBasis _ _ hfirstAmbient hsecondAmbient]
  rw [hfirstCycle, hsecondCycle]

end CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout
end CCM25Concrete
end Source
end ConnesWeilRH
