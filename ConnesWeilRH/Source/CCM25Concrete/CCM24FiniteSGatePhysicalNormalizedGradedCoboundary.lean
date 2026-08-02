/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction

/-!
# Normalized graded-coboundary reduction for the finite-S Gate target

The normalized double-boundary numerator has two Gram orders.  Their average
is the symmetric graded semicommutator, while their difference is exactly the
compressed detector/Gram coboundary.  After the inverse Gram is restored, the
latter becomes the ordered Gram-similarity anomaly.

The two terms remain one response.  No trace cycle, anomaly cancellation,
separate trace estimate, Gate 3U bound, finite-S sign, Burnol identity, or RH
premise is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalNormalizedGradedCoboundary

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
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
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

private theorem adjoint_sub_endomorphism
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) :
    (A - B)† = A† - B† := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

private theorem base_sub_left_comp_eq_adjoint_base_sub_right_comp
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (gram compression base : H →L[ℂ] H)
    (hgram : IsSelfAdjoint gram)
    (hcompression : IsSelfAdjoint compression)
    (hbase : IsSelfAdjoint base) :
    base - gram ∘L compression = (base - compression ∘L gram)† := by
  rw [adjoint_sub_endomorphism, ContinuousLinearMap.adjoint_comp,
    hgram.adjoint_eq, hcompression.adjoint_eq, hbase.adjoint_eq]

private theorem half_smul_add_adjoint_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    IsSelfAdjoint ((1 / 2 : ℂ) • (operator + operator†)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  have hhalfCast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    norm_num
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    rw [hhalfCast, starRingEnd_apply, Complex.star_def,
      Complex.conj_ofReal]
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint.map_add, hhalf,
    ContinuousLinearMap.adjoint_adjoint, add_comm]

/-- Compression of the fixed selected detector to the source Sonin carrier. -/
noncomputable def sourceDetectorCompression
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
    sourceInclusion lambda

theorem sourceDetectorCompression_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    IsSelfAdjoint (sourceDetectorCompression owner lambda) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact sourceDetectorCompression_adjoint_eq owner lambda

/-- Left Gram-order numerator.  It differs from the existing centered
numerator only by the order of the source detector compression and Gram. -/
noncomputable def finiteEulerLeftBoundaryNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
      finiteEulerFrame lambda family -
    finiteEulerGram lambda family ∘L sourceDetectorCompression owner lambda

/-- Right Gram-order numerator already used by the source response. -/
noncomputable def finiteEulerRightBoundaryNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  centeredGramNumerator owner lambda family

/-- The two unnormalized boundary numerators are Hilbert-space adjoints. -/
theorem finiteEulerLeftBoundaryNumerator_eq_right_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerLeftBoundaryNumerator owner lambda family =
      (finiteEulerRightBoundaryNumerator owner lambda family)† := by
  let compression := sourceDetectorCompression owner lambda
  let base := (finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
    finiteEulerFrame lambda family
  have hbase : IsSelfAdjoint base := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    exact frameDetectorCompression_adjoint_eq owner lambda family
  exact base_sub_left_comp_eq_adjoint_base_sub_right_comp
    (finiteEulerGram lambda family) compression base
    (finiteEulerGram_isSelfAdjoint lambda family)
    (sourceDetectorCompression_isSelfAdjoint owner lambda) hbase

/-- The entire left/right asymmetry is one source detector/Gram coboundary. -/
theorem finiteEulerLeft_sub_right_eq_gramCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerLeftBoundaryNumerator owner lambda family -
        finiteEulerRightBoundaryNumerator owner lambda family =
      sourceDetectorCompression owner lambda ∘L
          finiteEulerGram lambda family -
        finiteEulerGram lambda family ∘L
          sourceDetectorCompression owner lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerLeftBoundaryNumerator,
    finiteEulerRightBoundaryNumerator, centeredGramNumerator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
  abel

/-- The target is the inverse Gram followed by the left boundary numerator. -/
theorem finiteEulerTargetCommutatorResponse_eq_gramInv_leftBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerGramInv lambda family ∘L
        finiteEulerLeftBoundaryNumerator owner lambda family := by
  rw [← leftOrderedSourceGramResponse_eq_targetCommutator]
  apply ContinuousLinearMap.ext
  intro u
  have hcancel := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda =>
      operator (sourceDetectorCompression owner lambda u))
    (finiteEulerGramInv_comp_gram lambda family)
  simp only [leftOrderedSourceGramResponse,
    finiteEulerLeftBoundaryNumerator, sourceDetectorCompression,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  simp only [sourceDetectorCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hcancel
  rw [hcancel]

/-- The left Gram numerator is exactly Proof 747's ordered double boundary. -/
theorem finiteEulerLeftBoundaryNumerator_eq_doubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerLeftBoundaryNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L
        finiteEulerMetricBoundaryCommutator lambda family ∘L
          sourceBoundaryCommutator owner lambda ∘L
            sourceInclusion lambda := by
  let left := finiteEulerLeftBoundaryNumerator owner lambda family
  let boundary := (sourceInclusion lambda)† ∘L
    finiteEulerMetricBoundaryCommutator lambda family ∘L
      sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda
  have hproducts : finiteEulerGramInv lambda family ∘L left =
      finiteEulerGramInv lambda family ∘L boundary := by
    rw [← finiteEulerTargetCommutatorResponse_eq_gramInv_leftBoundary]
    exact finiteEulerTargetCommutatorResponse_eq_doubleBoundary
      owner lambda family
  apply ContinuousLinearMap.ext
  intro u
  have hproduct := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u) hproducts
  have hcancel (v : sourceSoninCarrier lambda) :
      finiteEulerGram lambda family
          (finiteEulerGramInv lambda family v) = v := by
    exact congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator v)
      (finiteEulerGram_comp_inv lambda family)
  change left u = boundary u
  calc
    left u = finiteEulerGram lambda family
        (finiteEulerGramInv lambda family (left u)) := (hcancel _).symm
    _ = finiteEulerGram lambda family
        (finiteEulerGramInv lambda family (boundary u)) := by
          exact congrArg (finiteEulerGram lambda family) hproduct
    _ = boundary u := hcancel _

/-- Source Gram after the same lower-factor normalization as the ambient
metric in Proof 747. -/
noncomputable def finiteEulerLowerFactorNormalizedSourceGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) •
    finiteEulerGram lambda family

theorem normalizedSourceGramInv_comp_normalizedSourceGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerLowerFactorNormalizedSourceGram lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hc : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  apply ContinuousLinearMap.ext
  intro u
  have hcancel := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u)
    (finiteEulerGramInv_comp_gram lambda family)
  simp only [finiteEulerNormalizedSourceGramInv,
    finiteEulerLowerFactorNormalizedSourceGram,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hc), one_smul]
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hcancel

/-- Lower-factor-normalized left boundary numerator. -/
noncomputable def finiteEulerNormalizedLeftBoundaryNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) •
    finiteEulerLeftBoundaryNumerator owner lambda family

/-- Lower-factor-normalized right boundary numerator. -/
noncomputable def finiteEulerNormalizedRightBoundaryNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) •
    finiteEulerRightBoundaryNumerator owner lambda family

/-- The normalized right numerator remains the adjoint of the normalized
left numerator because the lower-factor gauge is real. -/
theorem finiteEulerNormalizedLeftBoundaryNumerator_adjoint_eq_right
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerNormalizedLeftBoundaryNumerator owner lambda family)† =
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
  have hscalar :
      star (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) =
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ := by
    simp only [star_inv₀, star_pow, Complex.star_def, Complex.conj_ofReal]
  rw [finiteEulerNormalizedLeftBoundaryNumerator,
    finiteEulerNormalizedRightBoundaryNumerator,
    ContinuousLinearMap.adjoint.map_smulₛₗ]
  rw [show (starRingEnd ℂ)
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) =
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ by
    exact hscalar]
  have h := congrArg ContinuousLinearMap.adjoint
    (finiteEulerLeftBoundaryNumerator_eq_right_adjoint owner lambda family)
  exact congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda =>
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) • operator)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using h)

/-- The normalized left numerator is the ordered normalized double boundary. -/
theorem finiteEulerNormalizedLeftBoundaryNumerator_eq_doubleBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedLeftBoundaryNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L
        finiteEulerNormalizedMetricBoundaryCommutator lambda family ∘L
          sourceBoundaryCommutator owner lambda ∘L
            sourceInclusion lambda := by
  rw [finiteEulerNormalizedLeftBoundaryNumerator,
    finiteEulerNormalizedMetricBoundaryCommutator_eq_smul,
    finiteEulerLeftBoundaryNumerator_eq_doubleBoundary]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

/-- The normalized numerator difference is the normalized Gram coboundary. -/
theorem finiteEulerNormalizedLeft_sub_right_eq_gramCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedLeftBoundaryNumerator owner lambda family -
        finiteEulerNormalizedRightBoundaryNumerator owner lambda family =
      sourceDetectorCompression owner lambda ∘L
          finiteEulerLowerFactorNormalizedSourceGram lambda family -
        finiteEulerLowerFactorNormalizedSourceGram lambda family ∘L
          sourceDetectorCompression owner lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hcoboundary := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u)
    (finiteEulerLeft_sub_right_eq_gramCoboundary owner lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply] at hcoboundary
  simp only [finiteEulerNormalizedLeftBoundaryNumerator,
    finiteEulerNormalizedRightBoundaryNumerator,
    finiteEulerLowerFactorNormalizedSourceGram,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  simpa only [smul_sub] using congrArg
    (fun v =>
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) • v)
    hcoboundary

/-- Symmetric normalized graded-semicommutator numerator. -/
noncomputable def finiteEulerNormalizedSymmetricBoundaryNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (1 / 2 : ℂ) •
    (finiteEulerNormalizedLeftBoundaryNumerator owner lambda family +
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family)

/-- The symmetric normalized numerator is self-adjoint. -/
theorem finiteEulerNormalizedSymmetricBoundaryNumerator_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint
      (finiteEulerNormalizedSymmetricBoundaryNumerator
        owner lambda family) := by
  rw [finiteEulerNormalizedSymmetricBoundaryNumerator,
    ← finiteEulerNormalizedLeftBoundaryNumerator_adjoint_eq_right]
  exact half_smul_add_adjoint_isSelfAdjoint
    (finiteEulerNormalizedLeftBoundaryNumerator owner lambda family)

/-- Contractive inverse Gram followed by the symmetric normalized boundary. -/
noncomputable def finiteEulerNormalizedSymmetricBoundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  finiteEulerNormalizedSourceGramInv lambda family ∘L
    finiteEulerNormalizedSymmetricBoundaryNumerator owner lambda family

/-- Ordered Gram-similarity anomaly.  It is not asserted to vanish. -/
noncomputable def finiteEulerNormalizedGramSimilarityAnomaly
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (1 / 2 : ℂ) •
    (finiteEulerNormalizedSourceGramInv lambda family ∘L
        sourceDetectorCompression owner lambda ∘L
          finiteEulerLowerFactorNormalizedSourceGram lambda family -
      sourceDetectorCompression owner lambda)

/-- The anomaly is the inverse Gram applied to half the left/right
coboundary.  This identity uses no trace cycle. -/
theorem finiteEulerNormalizedGramSimilarityAnomaly_eq_boundaryDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedGramSimilarityAnomaly owner lambda family =
      (1 / 2 : ℂ) •
        (finiteEulerNormalizedSourceGramInv lambda family ∘L
          (finiteEulerNormalizedLeftBoundaryNumerator owner lambda family -
            finiteEulerNormalizedRightBoundaryNumerator
              owner lambda family)) := by
  rw [finiteEulerNormalizedLeft_sub_right_eq_gramCoboundary]
  apply ContinuousLinearMap.ext
  intro u
  have hcancel := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda =>
      operator (sourceDetectorCompression owner lambda u))
    (normalizedSourceGramInv_comp_normalizedSourceGram lambda family)
  simp only [finiteEulerNormalizedGramSimilarityAnomaly,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, map_sub]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hcancel
  rw [hcancel]

/-- The complete normalized graded-coboundary response.  Its two summands
must remain together until compact support has acted on the signed scalar. -/
noncomputable def finiteEulerNormalizedGradedCoboundaryResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family +
    finiteEulerNormalizedGramSimilarityAnomaly owner lambda family

theorem finiteEulerNormalizedGradedCoboundaryResponse_eq_leftBoundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedGradedCoboundaryResponse owner lambda family =
      finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
  rw [finiteEulerNormalizedGradedCoboundaryResponse,
    finiteEulerNormalizedSymmetricBoundaryResponse,
    finiteEulerNormalizedSymmetricBoundaryNumerator,
    finiteEulerNormalizedGramSimilarityAnomaly_eq_boundaryDifference]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    map_add, map_sub, map_smul]
  module

/-- Proof 747's target is exactly the combined symmetric-plus-anomaly owner. -/
theorem finiteEulerTargetCommutatorResponse_eq_normalizedGradedCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerNormalizedGradedCoboundaryResponse
        owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_normalizedDoubleBoundary,
    finiteEulerNormalizedDoubleBoundaryResponse,
    ← finiteEulerNormalizedLeftBoundaryNumerator_eq_doubleBoundary,
    finiteEulerNormalizedGradedCoboundaryResponse_eq_leftBoundary]

/-- The anomaly is exactly what separates the target from its symmetric
graded-semicommutator component. -/
theorem finiteEulerTarget_sub_symmetricBoundary_eq_similarityAnomaly
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family -
        finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family =
      finiteEulerNormalizedGramSimilarityAnomaly owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_normalizedGradedCoboundary,
    finiteEulerNormalizedGradedCoboundaryResponse]
  abel

/-- The ordinary target trace is unchanged by the combined graded-coboundary
readout.  The theorem does not split the trace across the two summands. -/
theorem ordinaryTraceAlong_targetCommutator_eq_normalizedGradedCoboundary
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedGradedCoboundaryResponse
          owner lambda family) := by
  rw [finiteEulerTargetCommutatorResponse_eq_normalizedGradedCoboundary]

/-- The route-facing Gate quantifiers land on the combined symmetric and
anomaly owner.  No separate bound for either summand is introduced. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_normalizedGradedCoboundary
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
        (finiteEulerNormalizedGradedCoboundaryResponse
          owner lambda family)‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        ‖ordinaryTraceAlong sourceBasis
          (finiteEulerNormalizedDoubleBoundaryResponse
            owner lambda family)‖ ≤ bound :=
      exists_uniform_lowerFactorGaugedTraceBound_iff_normalizedDoubleBoundary
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ := by
      simp only [← finiteEulerTargetCommutatorResponse_eq_normalizedDoubleBoundary,
        finiteEulerTargetCommutatorResponse_eq_normalizedGradedCoboundary]

end CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
end CCM25Concrete
end Source
end ConnesWeilRH
