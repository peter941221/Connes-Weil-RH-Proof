/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCoframe

/-!
# Normalized double-boundary reduction for the finite-S Gate target

Proof 746 leaves one physical coframe leakage paired with the fixed detector
boundary.  This module exposes the leakage as a second commutator, now with
the complete Euler metric.  A scalar gauge then puts the inverse source Gram
factor inside a family-uniform contraction.

The normalized metric commutator remains a complete signed family-dependent
object.  No norm bound for it or Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGatePhysicalObliqueShearReduction
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance targetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace (targetTransportedSoninCarrier lambda family) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

private theorem adjoint_sub_endomorphism
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) :
    (A - B)† = A† - B† := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

/-- Orthogonal projection onto the complement of the source Sonin range. -/
noncomputable def sourceSoninComplementProjection
    (lambda : CCM24SoninScale) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda

theorem sourceSoninComplementProjection_isSelfAdjoint
    (lambda : CCM24SoninScale) :
    IsSelfAdjoint (sourceSoninComplementProjection lambda) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [sourceSoninComplementProjection, adjoint_sub_endomorphism,
    ContinuousLinearMap.adjoint_id,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]

theorem sourceSoninProjection_comp_complement_eq_zero
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L sourceSoninComplementProjection lambda =
      0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hProjectionSq := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (show sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
        sourceSoninProjection lambda by
      simpa only [ContinuousLinearMap.mul_def] using
        (sourceSoninProjection_isStarProjection lambda).isIdempotentElem)
  simp only [sourceSoninComplementProjection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub, ContinuousLinearMap.zero_apply]
  simp only [ContinuousLinearMap.comp_apply] at hProjectionSq
  rw [hProjectionSq, sub_self]

theorem complement_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) :
    sourceSoninComplementProjection lambda ∘L sourceSoninProjection lambda =
      0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hProjectionSq := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (show sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
        sourceSoninProjection lambda by
      simpa only [ContinuousLinearMap.mul_def] using
        (sourceSoninProjection_isStarProjection lambda).isIdempotentElem)
  simp only [sourceSoninComplementProjection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  simp only [ContinuousLinearMap.comp_apply] at hProjectionSq
  rw [hProjectionSq, sub_self]

theorem finiteEulerAmbientGram_isSelfAdjoint
    (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerAmbientGram family) := by
  simpa only [finiteEulerAmbientGram, finiteEulerTransportOperator] using
    (ContinuousLinearMap.isPositive_adjoint_comp_self
      (finiteEulerTransportOperator family)).isSelfAdjoint

/-- The source metric-boundary orientation `[R,H_S]`. -/
noncomputable def finiteEulerMetricBoundaryCommutator
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceSoninProjection lambda ∘L finiteEulerAmbientGram family -
    finiteEulerAmbientGram family ∘L sourceSoninProjection lambda

theorem finiteEulerMetricBoundaryCommutator_adjoint_eq_neg
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerMetricBoundaryCommutator lambda family)† =
      -finiteEulerMetricBoundaryCommutator lambda family := by
  rw [finiteEulerMetricBoundaryCommutator, adjoint_sub_endomorphism,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (finiteEulerAmbientGram_isSelfAdjoint family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  abel

/-- Before taking its adjoint, the physical leakage is the complement of the
ambient metric coframe. -/
theorem sourcePhysicalCoframeLeakage_eq_complement_ambientGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourcePhysicalCoframeLeakage lambda family =
      sourceSoninComplementProjection lambda ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [← sourceSoninCoframeLeakage_eq_physical]
  rfl

/-- Raw adjoint crossing before the metric commutator is inserted. -/
theorem sourcePhysicalCoframeLeakage_adjoint_eq_ambientCrossing
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourcePhysicalCoframeLeakage lambda family)† =
      finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
        finiteEulerAmbientGram family ∘L
          sourceSoninComplementProjection lambda := by
  rw [sourcePhysicalCoframeLeakage_eq_complement_ambientGram]
  simp only [ContinuousLinearMap.adjoint_comp,
    (sourceSoninComplementProjection_isSelfAdjoint lambda).adjoint_eq,
    (finiteEulerAmbientGram_isSelfAdjoint family).adjoint_eq,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The leakage adjoint contains the genuine metric boundary `[R,H_S]`.
This deletes every scalar component of the ambient Euler metric. -/
theorem sourcePhysicalCoframeLeakage_adjoint_eq_metricBoundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourcePhysicalCoframeLeakage lambda family)† =
      finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
        finiteEulerMetricBoundaryCommutator lambda family ∘L
          sourceSoninComplementProjection lambda := by
  rw [sourcePhysicalCoframeLeakage_adjoint_eq_ambientCrossing]
  apply ContinuousLinearMap.ext
  intro u
  have hComplement := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (sourceSoninProjection_comp_complement_eq_zero lambda)
  have hReadback := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (finiteEulerAmbientGram family
        (sourceSoninComplementProjection lambda u)))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hComplement
  simp only [ContinuousLinearMap.comp_apply] at hReadback
  simp only [finiteEulerMetricBoundaryCommutator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [hComplement, hReadback]
  simp only [map_zero, sub_zero]

/-- The detector complement crossing is exactly the fixed source boundary
commutator applied to the source inclusion. -/
theorem complement_detector_inclusion_eq_sourceBoundaryCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSoninComplementProjection lambda ∘L detectorOperator owner ∘L
        sourceInclusion lambda =
      sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hSource := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  simp only [ContinuousLinearMap.comp_apply] at hSource
  simp only [sourceSoninComplementProjection, sourceBoundaryCommutator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hSource]

/-- Unnormalized double-boundary form of the active target. -/
theorem finiteEulerTargetCommutatorResponse_eq_doubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
        finiteEulerMetricBoundaryCommutator lambda family ∘L
          sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage,
    finiteEulerPhysicalCoframeLeakageResponse,
    sourcePhysicalCoframeLeakage_adjoint_eq_metricBoundary]
  apply ContinuousLinearMap.ext
  intro u
  have hBoundary := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (complement_detector_inclusion_eq_sourceBoundaryCommutator owner lambda)
  simpa only [ContinuousLinearMap.comp_apply] using congrArg
    (finiteEulerGramInv lambda family ∘L (sourceInclusion lambda)† ∘L
      finiteEulerMetricBoundaryCommutator lambda family) hBoundary

/-- The scalar-gauged inverse source Gram. -/
noncomputable def finiteEulerNormalizedSourceGramInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) •
    finiteEulerGramInv lambda family

/-- The normalized inverse source Gram is a product of the normalized exact
restricted inverse and its adjoint. -/
theorem finiteEulerNormalizedSourceGramInv_eq_restrictedInverseProduct
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedSourceGramInv lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerRestrictedInverse lambda family) ∘L
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerRestrictedInverse lambda family)† := by
  let c : ℂ := finiteEulerLowerFactor family.visiblePrimes
  let B := finiteEulerRestrictedInverse lambda family
  have hGram : finiteEulerGramInv lambda family = B ∘L B† := rfl
  have hstar : star c = c := by
    simp only [c, Complex.star_def, Complex.conj_ofReal]
  have hAdjoint : (c • B)† = c • B† := by
    simpa only [starRingEnd_apply, hstar] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ c B)
  rw [finiteEulerNormalizedSourceGramInv, hGram]
  change c ^ 2 • (B ∘L B†) = (c • B) ∘L (c • B)†
  rw [hAdjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_smul, pow_two]

/-- The normalized inverse source Gram is contractive independently of the
visible finite family. -/
theorem norm_finiteEulerNormalizedSourceGramInv_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖finiteEulerNormalizedSourceGramInv lambda family‖ ≤ 1 := by
  rw [finiteEulerNormalizedSourceGramInv_eq_restrictedInverseProduct]
  let inverse := (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
    finiteEulerRestrictedInverse lambda family
  have hinverse : ‖inverse‖ ≤ 1 := by
    simpa only [inverse] using
      norm_lowerFactor_smul_restrictedInverse_le_one lambda family
  have hinverseAdjoint : ‖inverse†‖ ≤ 1 := by
    calc
      ‖inverse†‖ = ‖inverse‖ :=
        ContinuousLinearMap.adjoint.norm_map inverse
      _ ≤ 1 := hinverse
  calc
    ‖inverse ∘L inverse†‖ ≤ ‖inverse‖ * ‖inverse†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hinverse hinverseAdjoint
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The ambient metric after dividing the transport by its Euler lower
factor. -/
noncomputable def finiteEulerLowerFactorNormalizedAmbientGram
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) •
    finiteEulerAmbientGram family

/-- The metric boundary of the lower-factor-normalized ambient metric. -/
noncomputable def finiteEulerNormalizedMetricBoundaryCommutator
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceSoninProjection lambda ∘L
      finiteEulerLowerFactorNormalizedAmbientGram family -
    finiteEulerLowerFactorNormalizedAmbientGram family ∘L
      sourceSoninProjection lambda

theorem finiteEulerNormalizedMetricBoundaryCommutator_eq_smul
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedMetricBoundaryCommutator lambda family =
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) •
        finiteEulerMetricBoundaryCommutator lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerNormalizedMetricBoundaryCommutator,
    finiteEulerLowerFactorNormalizedAmbientGram,
    finiteEulerMetricBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_sub]

/-- The final normalized double-boundary owner.  Its inverse Gram factor is
contractive; the normalized metric boundary remains unsplit. -/
noncomputable def finiteEulerNormalizedDoubleBoundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  finiteEulerNormalizedSourceGramInv lambda family ∘L
    (sourceInclusion lambda)† ∘L
      finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
        sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda

/-- Scalar gauge cancellation puts the active target exactly in normalized
double-boundary form. -/
theorem finiteEulerTargetCommutatorResponse_eq_normalizedDoubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerNormalizedDoubleBoundaryResponse owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_doubleBoundary]
  apply ContinuousLinearMap.ext
  intro u
  have hc : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  simp only [finiteEulerNormalizedDoubleBoundaryResponse,
    finiteEulerNormalizedSourceGramInv,
    finiteEulerNormalizedMetricBoundaryCommutator_eq_smul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hc), one_smul]

/-- The ordinary target trace is unchanged by the normalized double-boundary
readout. -/
theorem ordinaryTraceAlong_targetCommutator_eq_normalizedDoubleBoundary
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedDoubleBoundaryResponse
          owner lambda family) := by
  rw [finiteEulerTargetCommutatorResponse_eq_normalizedDoubleBoundary]

/-- The route-facing Gate quantifiers land on the normalized double-boundary
owner.  This transfers an exact equivalence and does not prove its bound. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_normalizedDoubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedDoubleBoundaryResponse
          owner lambda family)‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        ‖ordinaryTraceAlong sourceBasis
          (finiteEulerTargetCommutatorResponse
            owner lambda family)‖ ≤ bound :=
      exists_uniform_lowerFactorGaugedTraceBound_iff_targetCommutatorTraceBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ := by
      simp only [finiteEulerTargetCommutatorResponse_eq_normalizedDoubleBoundary]

end CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
end CCM25Concrete
end Source
end ConnesWeilRH
