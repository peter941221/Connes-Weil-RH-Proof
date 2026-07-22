/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovCompletedReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSourceFirstJetSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedEndpointSupportBound

/-!
# Absolute uniform bound for the corrected Schur--Markov cocycle

The Schur--Markov scalar gives a mixed normalization of the raw metric
coframe: the adjoint transport is divided by the upper Euler factor while the
dual frame is multiplied by the lower Euler factor.  Both factors are
contractions, so the mixed coframe is uniformly contractive.

This yields a finite-family-independent absolute bound for the complete
corrected signed cocycle.  It does not yield the additional Schur--Markov
scalar on the right-hand side required by Gate 3U.  The final equivalence
theorem records that stronger relative estimate exactly, without hiding it in
a producer premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurMarkovUniformBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSTransportBounds
open CCM24FiniteSCoframeResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSSourceFirstJetSupportBound
open CCM24FiniteSNormalizedEndpointSupportBound
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovCompletedReadout
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Mixed lower/upper normalization -/

/-- Dividing the adjoint finite-Euler transport by its exact upper product
makes it a contraction. -/
theorem norm_invUpperFactor_smul_finiteEulerTransportAdjoint_le_one
    (family : FinitePrimePowerFamily) :
    ‖((finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹) •
        (finiteEulerTransportOperator family)†‖ ≤ 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (finiteEulerUpperFactor_pos family.visiblePrimes),
    ContinuousLinearMap.adjoint.norm_map]
  have hupper : 0 ≤ (finiteEulerUpperFactor family.visiblePrimes)⁻¹ :=
    le_of_lt (inv_pos.mpr (finiteEulerUpperFactor_pos family.visiblePrimes))
  calc
    (finiteEulerUpperFactor family.visiblePrimes)⁻¹ *
        ‖finiteEulerTransportOperator family‖ ≤
      (finiteEulerUpperFactor family.visiblePrimes)⁻¹ *
        finiteEulerUpperFactor family.visiblePrimes := by
          exact mul_le_mul_of_nonneg_left
            (norm_finiteEulerTransportOperator_le_upperFactor
              family.visiblePrimes) hupper
    _ = 1 := inv_mul_cancel₀
      (ne_of_gt (finiteEulerUpperFactor_pos family.visiblePrimes))

/-- The exact Schur--Markov scaling of the raw metric coframe. -/
noncomputable def schurMarkovMixedMetricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
    finiteEulerMetricCoframe lambda family

/-- The mixed coframe factors into an upper-normalized adjoint transport and
a lower-normalized dual frame.  No inverse lower factor occurs. -/
theorem schurMarkovMixedMetricCoframe_eq_normalized_factors
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    schurMarkovMixedMetricCoframe lambda family =
      (((finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹) •
          (finiteEulerTransportOperator family)†) ∘L
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerDualFrame lambda family) := by
  rw [schurMarkovMixedMetricCoframe,
    finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame,
    suffixEulerSchurMarkovScalar_eq_lower_div_upper]
  have hscalar :
      ((finiteEulerLowerFactor family.visiblePrimes /
          finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ) =
        (finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹ *
          (finiteEulerLowerFactor family.visiblePrimes : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    ring
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul]
  rw [hscalar]
  module

/-- The mixed metric coframe is a contraction uniformly in the finite
visible-prime family. -/
theorem norm_schurMarkovMixedMetricCoframe_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖schurMarkovMixedMetricCoframe lambda family‖ ≤ 1 := by
  rw [schurMarkovMixedMetricCoframe_eq_normalized_factors]
  calc
    _ ≤ ‖((finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹ •
          (finiteEulerTransportOperator family)†)‖ *
        ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerDualFrame lambda family‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (norm_invUpperFactor_smul_finiteEulerTransportAdjoint_le_one family)
      (norm_lowerFactor_smul_finiteEulerDualFrame_le_one lambda family)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem primeSchurMarkovScalar_le_one (p : CCM24VisiblePrime) :
    primeSchurMarkovScalar p ≤ 1 := by
  rw [primeSchurMarkovScalar]
  apply (div_le_one (primeEulerUpperFactor_pos p)).mpr
  linarith [ccm24PrimeEulerCoefficient_nonneg p]

theorem suffixEulerSchurMarkovScalar_le_one
    (S : List CCM24VisiblePrime) :
    suffixEulerSchurMarkovScalar S ≤ 1 := by
  induction S with
  | nil => simp [suffixEulerSchurMarkovScalar]
  | cons p S ih =>
      change primeSchurMarkovScalar p * suffixEulerSchurMarkovScalar S ≤ 1
      calc
        _ ≤ 1 * 1 := mul_le_mul (primeSchurMarkovScalar_le_one p) ih
          (le_of_lt (suffixEulerSchurMarkovScalar_pos S)) zero_le_one
        _ = 1 := one_mul 1

/-! ## Mixed endpoint response -/

/-- The raw source endpoint with the single Schur--Markov scalar inserted
before taking its trace. -/
noncomputable def schurMarkovScaledSourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
    sourceBandGramResponse owner lambda family

theorem schurMarkovScaledSourceBandGramResponse_eq_mixedPhysical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    schurMarkovScaledSourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        schurMarkovMixedMetricCoframe lambda family) := by
  rw [schurMarkovScaledSourceBandGramResponse,
    sourceBandGramResponse_eq_neg_threeBranch,
    schurMarkovMixedMetricCoframe]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, finiteEulerMetricCoframe, map_smul,
    smul_neg]

/-! The next carrier cycle is generic in the coframe.  It is the same legal
two-Hilbert--Schmidt cycle used by the lower-square normalized endpoint, but
it does not choose a normalization. -/
set_option maxHeartbeats 3000000 in
-- Expanding the generic rectangular carrier cycle is elaboration intensive.
theorem sourceCoframeThreeBranchTrace_eq_ambient
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
    (coframe : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    ordinaryTraceAlong sourceBasis
        (-((sourceInclusion lambda)† ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          coframe)) =
      -ordinaryTraceAlong globalBasis
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          coframe ∘L (sourceInclusion lambda)†) := by
  let data := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let J := sourceInclusion lambda
  let sourcePair :=
    (BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
      data J coframe).smulRight (-1)
  let ambientRight := -(data.right ∘L coframe ∘L J.adjoint)
  have hSourceProduct : sourcePair.traceProduct =
      -((sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        coframe) := by
    dsimp only [sourcePair]
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq]
    dsimp only [data, J]
    rw [sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      neg_one_smul]
  have hAmbientRight : Summable fun i =>
      ‖ambientRight (globalBasis i)‖ ^ 2 := by
    have hprecomp := summable_normSq_precomp globalBasis boundaryBasis globalBasis
      data.right (coframe ∘L J.adjoint) data.right_summable_normSq
    simpa only [ambientRight, ContinuousLinearMap.neg_apply, norm_neg] using hprecomp
  have hSourceCycle :=
    sourcePair.ordinaryTraceAlong_traceProduct_eq_cyclic boundaryBasis
  have hAmbientCycle :=
    BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
      globalBasis boundaryBasis data.left ambientRight
      data.left_summable_normSq hAmbientRight
  rw [← hSourceProduct]
  calc
    ordinaryTraceAlong sourceBasis sourcePair.traceProduct =
        ordinaryTraceAlong boundaryBasis
          (sourcePair.right ∘L sourcePair.left.adjoint) := hSourceCycle
    _ = ordinaryTraceAlong boundaryBasis
        (ambientRight ∘L data.left.adjoint) := by
      apply congrArg (ordinaryTraceAlong boundaryBasis)
      dsimp only [sourcePair, ambientRight,
        BasisHilbertSchmidtPairData.smulRight,
        BasisHilbertSchmidtPairData.boundedPrecomp]
      rw [ContinuousLinearMap.adjoint_comp]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, neg_one_smul,
        ContinuousLinearMap.neg_apply]
    _ = ordinaryTraceAlong globalBasis
        (data.left.adjoint ∘L ambientRight) := hAmbientCycle.symm
    _ = -ordinaryTraceAlong globalBasis
        (data.traceProduct ∘L coframe ∘L J.adjoint) := by
      have hoperator : data.left.adjoint ∘L ambientRight =
          -(data.traceProduct ∘L coframe ∘L J.adjoint) := by
        apply ContinuousLinearMap.ext
        intro u
        dsimp only [ambientRight, BasisHilbertSchmidtPairData.traceProduct]
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.neg_apply, map_neg]
      rw [hoperator]
      simp only [ordinaryTraceAlong]
      rw [← tsum_neg]
      apply tsum_congr
      intro i
      exact inner_neg_right _ _
    _ = -ordinaryTraceAlong globalBasis
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          coframe ∘L (sourceInclusion lambda)†) := by
      dsimp only [data, J]
      rw [sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]

theorem schurMarkovScaledSourceBandGramTrace_norm_le_supportEnergy
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
    ‖ordinaryTraceAlong sourceBasis
        (schurMarkovScaledSourceBandGramResponse owner lambda family)‖ ≤
      (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  rw [schurMarkovScaledSourceBandGramResponse_eq_mixedPhysical,
    sourceCoframeThreeBranchTrace_eq_ambient owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor, norm_neg]
  let rightBounded := schurMarkovMixedMetricCoframe lambda family ∘L
    (sourceInclusion lambda)†
  have hJ : ‖(sourceInclusion lambda)†‖ ≤ 1 := by
    have hadjoint : ‖(sourceInclusion lambda)†‖ =
        ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hadjoint]
    exact Submodule.norm_subtypeL_le _
  have hright : ‖rightBounded‖ ≤ 1 := by
    dsimp only [rightBounded]
    calc
      _ ≤ ‖schurMarkovMixedMetricCoframe lambda family‖ *
          ‖(sourceInclusion lambda)†‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (norm_schurMarkovMixedMetricCoframe_le_one lambda family) hJ
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hid : ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]
  simpa only [ContinuousLinearMap.id_comp, rightBounded] using
    (sourceThreeBranchCommutator_boundedSandwich_trace_norm_le_supportEnergy
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor (ContinuousLinearMap.id ℂ finiteSCarrier)
      rightBounded hid hright)

/-! ## Complete corrected signed cocycle -/

set_option maxHeartbeats 3000000 in
-- The complete source trace expands two large physical pair owners.
/-- The complete corrected signed cocycle has an absolute support bound whose
constant is independent of the finite visible-prime family.  The cocycle is
kept whole until its exact first-jet-minus-endpoint trace identity is used;
no primewise absolute value appears. -/
theorem suffixEulerLowerFactorCompletedSignedCocycle_trace_norm_le_supportEnergy
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family)‖ ≤
      (18 + 6 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let rhoS := suffixEulerSchurMarkovScalar family.visiblePrimes
  let first := sourceActualBandFiniteEulerSoninResponse owner lambda family
  let endpoint := sourceBandGramResponse owner lambda family
  let remainder := sourceActualBandFiniteEulerRemainderResponse owner lambda family
  let gauged := lowerFactorGaugedActualBandCompletedRelativeResponse
    owner lambda family
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let Kfirst := (12 + 4 * H) * P
  let Kendpoint := (6 + 2 * H) * P
  have hrhoPos : 0 < rhoS := by
    dsimp only [rhoS]
    exact suffixEulerSchurMarkovScalar_pos family.visiblePrimes
  have hrho : rhoS ≤ 1 := by
    dsimp only [rhoS]
    exact suffixEulerSchurMarkovScalar_le_one family.visiblePrimes
  have hfirstClass : IsTraceClassAlong sourceBasis first := by
    dsimp only [first]
    exact sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hendpointClass : IsTraceClassAlong sourceBasis endpoint := by
    dsimp only [endpoint]
    exact sourceBandGramResponse_isTraceClassAlong owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hremainderClass : IsTraceClassAlong sourceBasis remainder := by
    dsimp only [remainder]
    exact sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hgaugedClass : IsTraceClassAlong sourceBasis gauged := by
    dsimp only [gauged]
    rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder]
    exact hremainderClass
  have htraceC :=
    ordinaryTraceAlong_suffixEulerCompletedSignedCocycle_eq_scaledResponse
      owner lambda family sourceBasis hgaugedClass
  have hremTrace : ordinaryTraceAlong sourceBasis remainder =
      ordinaryTraceAlong sourceBasis first -
        ordinaryTraceAlong sourceBasis endpoint := by
    dsimp only [remainder, first, endpoint]
    rw [sourceActualBandFiniteEulerRemainderResponse]
    exact ordinaryTraceAlong_sub sourceBasis _ _ hfirstClass hendpointClass
  have htraceC' :
      ordinaryTraceAlong sourceBasis
          (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family) =
        (rhoS : ℂ) *
          (ordinaryTraceAlong sourceBasis first -
            ordinaryTraceAlong sourceBasis endpoint) := by
    calc
      _ = (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
          ordinaryTraceAlong sourceBasis
            (lowerFactorGaugedActualBandCompletedRelativeResponse
              owner lambda family) := htraceC
      _ = (rhoS : ℂ) * ordinaryTraceAlong sourceBasis remainder := by
        rw [lowerFactorGaugedActualBandCompletedRelativeResponse_eq_sourceRemainder]
      _ = (rhoS : ℂ) *
          (ordinaryTraceAlong sourceBasis first -
            ordinaryTraceAlong sourceBasis endpoint) := by
        rw [hremTrace]
  have hfirstBound : ‖ordinaryTraceAlong sourceBasis first‖ ≤ Kfirst := by
    dsimp only [first, Kfirst, H, P]
    exact sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hscaledFirst :
      ‖(rhoS : ℂ) * ordinaryTraceAlong sourceBasis first‖ ≤ Kfirst := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrhoPos]
    calc
      rhoS * ‖ordinaryTraceAlong sourceBasis first‖ ≤
          1 * ‖ordinaryTraceAlong sourceBasis first‖ := by
        exact mul_le_mul_of_nonneg_right hrho (norm_nonneg _)
      _ ≤ 1 * Kfirst := mul_le_mul_of_nonneg_left hfirstBound zero_le_one
      _ = Kfirst := one_mul _
  have hscaledEndpointResponse :
      ‖ordinaryTraceAlong sourceBasis
        (schurMarkovScaledSourceBandGramResponse owner lambda family)‖ ≤
          Kendpoint := by
    dsimp only [Kendpoint, H, P]
    exact schurMarkovScaledSourceBandGramTrace_norm_le_supportEnergy owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hscaledEndpointTrace :
      ordinaryTraceAlong sourceBasis
          (schurMarkovScaledSourceBandGramResponse owner lambda family) =
        (rhoS : ℂ) * ordinaryTraceAlong sourceBasis endpoint := by
    rw [schurMarkovScaledSourceBandGramResponse]
    dsimp only [rhoS, endpoint]
    exact ordinaryTraceAlong_smul sourceBasis _ _ hendpointClass
  have hscaledEndpoint :
      ‖(rhoS : ℂ) * ordinaryTraceAlong sourceBasis endpoint‖ ≤
        Kendpoint := by
    rw [← hscaledEndpointTrace]
    exact hscaledEndpointResponse
  calc
    ‖ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family)‖ =
      ‖(rhoS : ℂ) * ordinaryTraceAlong sourceBasis first -
        (rhoS : ℂ) * ordinaryTraceAlong sourceBasis endpoint‖ := by
          rw [htraceC', mul_sub]
    _ ≤ ‖(rhoS : ℂ) * ordinaryTraceAlong sourceBasis first‖ +
        ‖(rhoS : ℂ) * ordinaryTraceAlong sourceBasis endpoint‖ :=
      norm_sub_le _ _
    _ ≤ Kfirst + Kendpoint := add_le_add hscaledFirst hscaledEndpoint
    _ = (18 + 6 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      dsimp only [Kfirst, Kendpoint, H, P]
      ring

/-- The still-missing relative Schur--Markov estimate is exactly equivalent
to the raw completed-response estimate.  This theorem prevents the absolute
uniform bound above from being misread as the additional `rho_S` gain. -/
theorem suffixEulerCompletedSignedCocycle_relative_bound_iff_raw_bound
    {ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hresponse : IsTraceClassAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family))
    (bound : ℝ) :
    ‖ordinaryTraceAlong sourceBasis
        (suffixEulerLowerFactorCompletedSignedCocycle owner lambda family)‖ ≤
        suffixEulerSchurMarkovScalar family.visiblePrimes * bound ↔
      ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound := by
  rw [ordinaryTraceAlong_suffixEulerCompletedSignedCocycle_eq_scaledResponse
    owner lambda family sourceBasis hresponse,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suffixEulerSchurMarkovScalar_pos family.visiblePrimes)]
  constructor
  · intro h
    nlinarith [suffixEulerSchurMarkovScalar_pos family.visiblePrimes]
  · intro h
    exact mul_le_mul_of_nonneg_left h
      (le_of_lt (suffixEulerSchurMarkovScalar_pos family.visiblePrimes))

end CCM24FiniteSSchurMarkovUniformBound
end CCM25Concrete
end Source
end ConnesWeilRH
