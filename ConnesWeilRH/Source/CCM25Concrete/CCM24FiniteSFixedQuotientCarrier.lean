/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInputSideTraceConsumer

/-!
# The actual fixed-quotient band carrier

The fixed-quotient first jet acts on the source band `B = E - R`, not on the
source Sonin carrier `R`.  This module makes that carrier distinction
explicit.  It also records the semantic guard that precomposing a band
corner with the Sonin inclusion kills it identically.

No Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedQuotientCarrier

open MeasureTheory
open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalSupport
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSBandTrace
open CCM24SourceProlateTrace
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientFirstJet
open scoped InnerProduct

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The source band `B = E - R` is an orthogonal projection because
`R <= E`. -/
theorem sourceBandProjection_isStarProjection (lambda : CCM24SoninScale) :
    IsStarProjection (sourceBandProjection lambda) := by
  unfold sourceBandProjection
  apply (sourceSoninProjection_isStarProjection lambda).sub_of_mul_eq_left
    (radialSupportProjection_isStarProjection lambda)
  simpa only [ContinuousLinearMap.mul_def] using
    sourceSoninProjection_comp_radialSupportProjection lambda

/-- The closed range of the genuine source quotient-band projection. -/
noncomputable def sourceBandClosedRange (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ finiteSCarrier where
  toSubmodule := (sourceBandProjection lambda).range
  isClosed' :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (sourceBandProjection_isStarProjection lambda).isIdempotentElem

theorem sourceBandProjection_eq_starProjection (lambda : CCM24SoninScale) :
    sourceBandProjection lambda =
      (sourceBandClosedRange lambda).starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext
    (sourceBandProjection_isStarProjection lambda)
    isStarProjection_starProjection
  rw [Submodule.range_starProjection]
  rfl

/-- Hilbert carrier of the fixed quotient `E H = R H ⊕ B H`, restricted to
the moving band summand `B H`. -/
noncomputable abbrev sourceBandCarrier (lambda : CCM24SoninScale) :=
  (sourceBandClosedRange lambda).toSubmodule

noncomputable local instance sourceBandCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceBandCarrier lambda) :=
  (sourceBandClosedRange lambda).isClosed.completeSpace_coe

/-- Isometric inclusion of the genuine quotient-band carrier. -/
noncomputable def sourceBandInclusion (lambda : CCM24SoninScale) :
    sourceBandCarrier lambda →L[ℂ] finiteSCarrier :=
  (sourceBandClosedRange lambda).toSubmodule.subtypeL

theorem sourceBandInclusion_adjoint_comp_self (lambda : CCM24SoninScale) :
    (sourceBandInclusion lambda)† ∘L sourceBandInclusion lambda =
      ContinuousLinearMap.id ℂ (sourceBandCarrier lambda) := by
  rw [sourceBandInclusion, Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  exact (sourceBandClosedRange lambda).toSubmodule
    |>.starProjection_mem_subspace_eq_self u

theorem sourceBandInclusion_comp_adjoint (lambda : CCM24SoninScale) :
    sourceBandInclusion lambda ∘L (sourceBandInclusion lambda)† =
      sourceBandProjection lambda := by
  rw [sourceBandInclusion, Submodule.adjoint_subtypeL,
    sourceBandProjection_eq_starProjection]
  rfl

theorem sourceBandProjection_comp_sourceBandInclusion
    (lambda : CCM24SoninScale) :
    sourceBandProjection lambda ∘L sourceBandInclusion lambda =
      sourceBandInclusion lambda := by
  rw [sourceBandProjection_eq_starProjection]
  apply ContinuousLinearMap.ext
  intro u
  exact (sourceBandClosedRange lambda).toSubmodule
    |>.starProjection_mem_subspace_eq_self u

/-- Semantic guard: the old Sonin inclusion lands in `R`, so the quotient
band projection `B = E - R` kills it. -/
theorem sourceBandProjection_comp_sourceInclusion_eq_zero
    (lambda : CCM24SoninScale) :
    sourceBandProjection lambda ∘L sourceInclusion lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hradial := DFunLike.congr_fun
    (radialSupportProjection_comp_sourceInclusion lambda) u
  simp only [ContinuousLinearMap.comp_apply] at hradial
  have hsonin :
      sourceSoninProjection lambda (sourceInclusion lambda u) =
        sourceInclusion lambda u := by
    have hJJ := sourceInclusion_comp_adjoint lambda
    have hJdJ := sourceInclusion_adjoint_comp_self lambda
    calc
      sourceSoninProjection lambda (sourceInclusion lambda u) =
          (sourceInclusion lambda ∘L (sourceInclusion lambda)†)
            (sourceInclusion lambda u) := by rw [hJJ]
      _ = sourceInclusion lambda
          (((sourceInclusion lambda)† ∘L sourceInclusion lambda) u) := rfl
      _ = sourceInclusion lambda u := by rw [hJdJ]; rfl
  simp only [ContinuousLinearMap.comp_apply, sourceBandProjection,
    ContinuousLinearMap.sub_apply,
    hradial, hsonin, sub_self, ContinuousLinearMap.zero_apply]

/-- Any ambient operator prefix still sees zero after the invalid
Sonin-to-band precomposition. -/
theorem comp_sourceBandProjection_comp_sourceInclusion_eq_zero
    (lambda : CCM24SoninScale)
    (left : finiteSCarrier →L[ℂ] finiteSCarrier) :
    left ∘L sourceBandProjection lambda ∘L sourceInclusion lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero := DFunLike.congr_fun
    (sourceBandProjection_comp_sourceInclusion_eq_zero lambda) u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  rw [hzero, map_zero]

/-- The literal old source-Sonin precomposition of the fixed-quotient corner
is zero, independently of the detector and transport. -/
theorem sourceFixedQuotientCorner_on_sourceSoninCarrier_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceInclusion lambda)† ∘L sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda ∘L sourceInclusion lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero := DFunLike.congr_fun
    (sourceBandProjection_comp_sourceInclusion_eq_zero lambda) u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero ⊢
  simp only [hzero, map_zero]

/-- The two surviving Proof 405 branches on the corrected quotient-band
carrier.  This is the existing ambient identity precomposed by `J_B` rather
than by the annihilated Sonin inclusion `J_R`. -/
theorem sourceBandFixedQuotientCorner_eq_secondSupport_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda ∘L sourceBandInclusion lambda =
      (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L sourceSoninProjection lambda ∘L
          transport ∘L sourceBandProjection lambda ∘L
          sourceBandInclusion lambda +
        (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceSoninProjection lambda ∘L transport ∘L
          sourceBandProjection lambda ∘L sourceBandInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (sourceFixedQuotientCorner_eq_secondSupport_twoBranch
      owner lambda transport) (sourceBandInclusion lambda u)
  have h' := congrArg ((sourceBandInclusion lambda)†) h
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add] using h'

/-!
The corrected input-side producer keeps the existing ambient four-coordinate
pair and changes only the precomposition carrier from `Ran(R)` to `Ran(B)`.
This preserves all fixed-`S` Hilbert--Schmidt and trace-legality data already
owned by the ambient pair.
-/
set_option maxHeartbeats 800000 in
-- The complete four-coordinate boundary carrier is expensive to elaborate.
noncomputable def sourceBandFixedQuotientFirstJetInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    InputSideRootS2Producer
      (K := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      (G := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      bandBasis :=
  inputSideRootS2ProducerOfPairData
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      boundaryBasis bandBasis
      (sourceFixedQuotientFirstJetPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor transport)
      (sourceBandInclusion lambda) (sourceBandInclusion lambda))

set_option maxHeartbeats 800000 in
-- Unfolding the corrected producer exposes the complete boundary pair.
theorem sourceBandFixedQuotientFirstJetInputSideProducer_response_eq_corner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceBandFixedQuotientFirstJetInputSideProducer owner lambda a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      bandBasis hfactor transport).response =
      (sourceBandInclusion lambda)† ∘L sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner))
          (sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda)) ∘L
        sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) ∘L transport ∘L
        sourceBandProjection lambda ∘L sourceBandInclusion lambda := by
  rw [sourceBandFixedQuotientFirstJetInputSideProducer,
    inputSideRootS2ProducerOfPairData_response_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceFixedQuotientFirstJetPairData_traceProduct_eq_corner owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor transport]
  apply ContinuousLinearMap.ext
  intro u
  rfl

end CCM24FiniteSFixedQuotientCarrier
end CCM25Concrete
end Source
end ConnesWeilRH
