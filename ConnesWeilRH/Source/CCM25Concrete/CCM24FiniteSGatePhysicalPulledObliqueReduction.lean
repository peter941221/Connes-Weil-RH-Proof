/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalTargetCommutatorReduction

/-!
# Pulled-oblique reduction for the finite-S Gate trace

Conjugating the actual target Sonin projection by the finite Euler transport
gives an oblique projection on the fixed source ambient carrier.  It fixes the
source Sonin range.  The target-commutator response can therefore be written
with all detector dependence inside the fixed source commutator `[W, R]`.

No trace cycle, factorwise transport estimate, or family-uniform bound is
asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPulledObliqueReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual target Sonin projection pulled back to the fixed source
ambient carrier: `Q_S=T_S^-1 P_S T_S`. -/
noncomputable def finiteEulerPulledTargetProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  finiteEulerInverseOperator family ∘L
    targetSoninProjection lambda family ∘L
      finiteEulerTransportOperator family

/-- The pulled target projection is genuinely idempotent, though generally
not orthogonal on the fixed source ambient carrier. -/
theorem finiteEulerPulledTargetProjection_comp_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledTargetProjection lambda family ∘L
        finiteEulerPulledTargetProjection lambda family =
      finiteEulerPulledTargetProjection lambda family := by
  have hProjectionSq :
      targetSoninProjection lambda family ∘L
          targetSoninProjection lambda family =
        targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      (targetSoninProjection_isStarProjection lambda family).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  have hRetraction := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (targetSoninProjection lambda family
        (finiteEulerTransportOperator family u)))
    (transport_comp_inverse family)
  have hProjectionSqApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (finiteEulerTransportOperator family u))
    hProjectionSq
  simp only [finiteEulerPulledTargetProjection,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hRetraction hProjectionSqApply
  rw [hRetraction, hProjectionSqApply]

/-- The pulled target projection fixes the source Sonin inclusion:
`Q_S J=J`. -/
theorem finiteEulerPulledTargetProjection_comp_sourceInclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledTargetProjection lambda family ∘L
        sourceInclusion lambda =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hProjectionFix := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (targetSoninProjection_comp_transport_frame lambda family)
  have hInverse := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (sourceInclusion lambda u))
    (inverse_comp_transport family)
  simp only [finiteEulerPulledTargetProjection,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.comp_apply] at hProjectionFix
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hInverse
  rw [hProjectionFix, hInverse]

/-- The pulled target projection fixes the whole source Sonin projection:
`Q_S R=R`. -/
theorem finiteEulerPulledTargetProjection_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledTargetProjection lambda family ∘L
        sourceSoninProjection lambda =
      sourceSoninProjection lambda := by
  rw [← sourceInclusion_comp_adjoint lambda]
  apply ContinuousLinearMap.ext
  intro u
  have hFix := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (((sourceInclusion lambda)†) u))
    (finiteEulerPulledTargetProjection_comp_sourceInclusion lambda family)
  simpa only [ContinuousLinearMap.comp_apply] using hFix

/-- First pulled form of the target response.  It contains the difference of
the oblique pulled projection from the identity. -/
theorem finiteEulerTargetCommutatorResponse_eq_pulledProjectionDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
        (finiteEulerPulledTargetProjection lambda family -
          ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        detectorOperator owner ∘L sourceInclusion lambda := by
  have hProjectionSq :
      targetSoninProjection lambda family ∘L
          targetSoninProjection lambda family =
        targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      (targetSoninProjection_isStarProjection lambda family).isIdempotentElem
  have hDetectorCommutes :
      detectorOperator owner ∘L finiteEulerTransportOperator family =
        finiteEulerTransportOperator family ∘L detectorOperator owner := by
    simpa only [finiteEulerTransportOperator] using
      (detectorOperator_comp_finiteEulerTransport owner
        family.visiblePrimes)
  apply ContinuousLinearMap.ext
  intro u
  have hProjectionFix := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (targetSoninProjection_comp_transport_frame lambda family)
  have hProjectionSqApply (x : finiteSCarrier) :
      targetSoninProjection lambda family
          (targetSoninProjection lambda family x) =
        targetSoninProjection lambda family x := by
    have hx := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
      hProjectionSq
    simpa only [ContinuousLinearMap.comp_apply] using hx
  have hCrossing :
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          targetSoninProjection lambda family)
          (finiteEulerTargetDetectorCommutator owner lambda family
            (finiteEulerTransportOperator family
              (sourceInclusion lambda u))) =
        (ContinuousLinearMap.id ℂ finiteSCarrier -
          targetSoninProjection lambda family)
          (detectorOperator owner
            (finiteEulerTransportOperator family
              (sourceInclusion lambda u))) := by
    simp only [finiteEulerTargetDetectorCommutator,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub]
    simp only [ContinuousLinearMap.comp_apply] at hProjectionFix
    rw [hProjectionFix, hProjectionSqApply]
    abel
  have hDetectorCommutesApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (sourceInclusion lambda u))
    hDetectorCommutes
  have hInverse := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (detectorOperator owner (sourceInclusion lambda u)))
    (inverse_comp_transport family)
  simp only [ContinuousLinearMap.comp_apply] at hDetectorCommutesApply
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hInverse
  simp only [finiteEulerTargetCommutatorResponse,
    finiteEulerPulledTargetProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply]
  rw [hCrossing, hDetectorCommutesApply]
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hInverse]
  abel

/-- The active pulled owner.  Every detector-dependent factor is now inside
the fixed source commutator `[W,R]`; only `Q_S` depends on the finite family. -/
noncomputable def finiteEulerPulledSourceCommutatorResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    finiteEulerPulledTargetProjection lambda family ∘L
      sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda

/-- The actual target response is exactly the pulled fixed-source commutator
response `J† Q_S [W,R] J`. -/
theorem finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerPulledSourceCommutatorResponse owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_pulledProjectionDifference]
  apply ContinuousLinearMap.ext
  intro u
  have hSourceFix :
      sourceSoninProjection lambda (sourceInclusion lambda u) =
        sourceInclusion lambda u := by
    rw [← sourceInclusion_comp_adjoint lambda]
    have hIsometry := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator u)
      (sourceInclusion_adjoint_comp_self lambda)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hIsometry
    simp only [ContinuousLinearMap.comp_apply]
    rw [hIsometry]
  have hPulledSource := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (detectorOperator owner (sourceInclusion lambda u)))
    (finiteEulerPulledTargetProjection_comp_sourceSoninProjection
      lambda family)
  have hAdjointSource := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda u)))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [finiteEulerPulledSourceCommutatorResponse,
    sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  simp only [ContinuousLinearMap.comp_apply] at hPulledSource hAdjointSource
  rw [hSourceFix, hPulledSource, hAdjointSource]

/-- The ordinary trace of the actual target response is the ordinary trace
of the fixed-source commutator owner, without cycling either product. -/
theorem ordinaryTraceAlong_targetCommutator_eq_pulledSourceCommutator
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (finiteEulerPulledSourceCommutatorResponse
          owner lambda family) := by
  rw [finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator]

/-- Fixed-family trace legality transfers to the pulled fixed-source owner by
the exact operator identity. -/
theorem pulledSourceCommutatorResponse_isTraceClassAlong_of_target
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (htarget : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)) :
    IsTraceClassAlong sourceBasis
      (finiteEulerPulledSourceCommutatorResponse owner lambda family) := by
  rw [← finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator]
  exact htarget

/-- Uniform target-response boundedness is exactly uniform boundedness of the
pulled fixed-source commutator response. -/
theorem exists_uniform_targetCommutatorTraceBound_iff_pulledSourceBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerPulledSourceCommutatorResponse
          owner lambda family)‖ ≤ bound) := by
  simp only [finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator]

/-- Proof 743's Gate reduction now lands on a fixed source commutator.  The
family dependence is confined to the pulled oblique projection `Q_S`. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_pulledSourceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
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
        (finiteEulerPulledSourceCommutatorResponse
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
    _ ↔ _ :=
      exists_uniform_targetCommutatorTraceBound_iff_pulledSourceBound
        owner lambda sourceBasis

end CCM24FiniteSGatePhysicalPulledObliqueReduction
end CCM25Concrete
end Source
end ConnesWeilRH
